import Mathbin.Algebra.Module.Basic 
import Mathbin.LinearAlgebra.Basic 
import Mathbin.Tactic.Abel 
import Mathbin.Data.Equiv.RingAut

/-!
# Algebras over commutative semirings

In this file we define `algebra`s over commutative (semi)rings, algebra homomorphisms `alg_hom`,
and algebra equivalences `alg_equiv`.
We also define the usual operations on `alg_hom`s (`id`, `comp`).

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

If `S` is an `R`-algebra and `A` is an `S`-algebra then `algebra.comap.algebra R S A` can be used
to provide `A` with a structure of an `R`-algebra. Other than that, `algebra.comap` is now
deprecated and replaced with `is_scalar_tower`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/


universe u v w u₁ v₁

open_locale BigOperators

section Prio

set_option extends_priority 200

/--
Given a commutative (semi)ring `R`, an `R`-algebra is a (possibly noncommutative)
(semi)ring `A` endowed with a morphism of rings `R →+* A` which lands in the
center of `A`.

For convenience, this typeclass extends `has_scalar R A` where the scalar action must
agree with left multiplication by the image of the structure morphism.

Given an `algebra R A` instance, the structure morphism `R →+* A` is denoted `algebra_map R A`.
-/
@[nolint has_inhabited_instance]
class Algebra(R : Type u)(A : Type v)[CommSemiringₓ R][Semiringₓ A] extends HasScalar R A, R →+* A where 
  commutes' : ∀ r x, (to_fun r*x) = x*to_fun r 
  smul_def' : ∀ r x, r • x = to_fun r*x

end Prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebraMap (R : Type u) (A : Type v) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] : R →+* A :=
  Algebra.toRingHom

/-- Creating an algebra from a morphism to the center of a semiring. -/
def RingHom.toAlgebra' {R S} [CommSemiringₓ R] [Semiringₓ S] (i : R →+* S) (h : ∀ c x, (i c*x) = x*i c) : Algebra R S :=
  { smul := fun c x => i c*x, commutes' := h, smul_def' := fun c x => rfl, toRingHom := i }

/-- Creating an algebra from a morphism to a commutative semiring. -/
def RingHom.toAlgebra {R S} [CommSemiringₓ R] [CommSemiringₓ S] (i : R →+* S) : Algebra R S :=
  i.to_algebra'$ fun _ => mul_commₓ _

theorem RingHom.algebra_map_to_algebra {R S} [CommSemiringₓ R] [CommSemiringₓ S] (i : R →+* S) :
  @algebraMap R S _ _ i.to_algebra = i :=
  rfl

namespace Algebra

variable{R : Type u}{S : Type v}{A : Type w}{B : Type _}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`.

See note [reducible non-instances]. -/
@[reducible]
def of_module' [CommSemiringₓ R] [Semiringₓ A] [Module R A] (h₁ : ∀ (r : R) (x : A), ((r • 1)*x) = r • x)
  (h₂ : ∀ (r : R) (x : A), (x*r • 1) = r • x) : Algebra R A :=
  { toFun := fun r => r • 1, map_one' := one_smul _ _,
    map_mul' :=
      fun r₁ r₂ =>
        by 
          rw [h₁, mul_smul],
    map_zero' := zero_smul _ _, map_add' := fun r₁ r₂ => add_smul r₁ r₂ 1,
    commutes' :=
      fun r x =>
        by 
          simp only [h₁, h₂],
    smul_def' :=
      fun r x =>
        by 
          simp only [h₁] }

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`.

See note [reducible non-instances]. -/
@[reducible]
def of_module [CommSemiringₓ R] [Semiringₓ A] [Module R A] (h₁ : ∀ (r : R) (x y : A), ((r • x)*y) = r • x*y)
  (h₂ : ∀ (r : R) (x y : A), (x*r • y) = r • x*y) : Algebra R A :=
  of_module'
    (fun r x =>
      by 
        rw [h₁, one_mulₓ])
    fun r x =>
      by 
        rw [h₂, mul_oneₓ]

section Semiringₓ

variable[CommSemiringₓ R][CommSemiringₓ S]

variable[Semiringₓ A][Algebra R A][Semiringₓ B][Algebra R B]

/-- We keep this lemma private because it picks up the `algebra.to_has_scalar` instance
which we set to priority 0 shortly. See `smul_def` below for the public version. -/
private theorem smul_def'' (r : R) (x : A) : r • x = algebraMap R A r*x :=
  Algebra.smul_def' r x

-- error in Algebra.Algebra.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
@[ext #[]]
theorem algebra_ext
{R : Type*}
[comm_semiring R]
{A : Type*}
[semiring A]
(P Q : algebra R A)
(w : ∀
 r : R, «expr = »(by { haveI [] [] [":=", expr P],
    exact [expr algebra_map R A r] }, by { haveI [] [] [":=", expr Q],
    exact [expr algebra_map R A r] })) : «expr = »(P, Q) :=
begin
  unfreezingI { rcases [expr P, "with", "⟨", "⟨", ident P, "⟩", "⟩"],
    rcases [expr Q, "with", "⟨", "⟨", ident Q, "⟩", "⟩"] },
  congr,
  { funext [ident r, ident a],
    replace [ident w] [] [":=", expr congr_arg (λ s, «expr * »(s, a)) (w r)],
    simp [] [] ["only"] ["[", "<-", expr smul_def'', "]"] [] ["at", ident w],
    apply [expr w] },
  { ext [] [ident r] [],
    exact [expr w r] },
  { apply [expr proof_irrel_heq] },
  { apply [expr proof_irrel_heq] }
end

instance (priority := 200)to_module : Module R A :=
  { one_smul :=
      by 
        simp [smul_def''],
    mul_smul :=
      by 
        simp [smul_def'', mul_assocₓ],
    smul_add :=
      by 
        simp [smul_def'', mul_addₓ],
    smul_zero :=
      by 
        simp [smul_def''],
    add_smul :=
      by 
        simp [smul_def'', add_mulₓ],
    zero_smul :=
      by 
        simp [smul_def''] }

attribute [instance] Algebra.toHasScalar

theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r*x :=
  Algebra.smul_def' r x

theorem algebra_map_eq_smul_one (r : R) : algebraMap R A r = r • 1 :=
  calc algebraMap R A r = algebraMap R A r*1 := (mul_oneₓ _).symm 
    _ = r • 1 := (Algebra.smul_def r 1).symm
    

theorem algebra_map_eq_smul_one' : «expr⇑ » (algebraMap R A) = fun r => r • (1 : A) :=
  funext algebra_map_eq_smul_one

/-- `mul_comm` for `algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : (algebraMap R A r*x) = x*algebraMap R A r :=
  Algebra.commutes' r x

/-- `mul_left_comm` for `algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) : (x*algebraMap R A r*y) = algebraMap R A r*x*y :=
  by 
    rw [←mul_assocₓ, ←commutes, mul_assocₓ]

/-- `mul_right_comm` for `algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) : ((x*algebraMap R A r)*y) = (x*y)*algebraMap R A r :=
  by 
    rw [mul_assocₓ, commutes, ←mul_assocₓ]

instance _root_.is_scalar_tower.right : IsScalarTower R A A :=
  ⟨fun x y z =>
      by 
        rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assocₓ]⟩

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem mul_smul_comm (s : R) (x y : A) : (x*s • y) = s • x*y :=
  by 
    rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem smul_mul_assoc (r : R) (x y : A) : ((r • x)*y) = r • x*y :=
  smul_mul_assoc r x y

section 

variable{r : R}{a : A}

@[simp]
theorem bit0_smul_one : bit0 r • (1 : A) = bit0 (r • (1 : A)) :=
  by 
    simp [bit0, add_smul]

theorem bit0_smul_one' : bit0 r • (1 : A) = r • 2 :=
  by 
    simp [bit0, add_smul, smul_add]

@[simp]
theorem bit0_smul_bit0 : bit0 r • bit0 a = r • bit0 (bit0 a) :=
  by 
    simp [bit0, add_smul, smul_add]

@[simp]
theorem bit0_smul_bit1 : bit0 r • bit1 a = r • bit0 (bit1 a) :=
  by 
    simp [bit0, add_smul, smul_add]

@[simp]
theorem bit1_smul_one : bit1 r • (1 : A) = bit1 (r • (1 : A)) :=
  by 
    simp [bit1, add_smul]

theorem bit1_smul_one' : bit1 r • (1 : A) = (r • 2)+1 :=
  by 
    simp [bit1, bit0, add_smul, smul_add]

@[simp]
theorem bit1_smul_bit0 : bit1 r • bit0 a = (r • bit0 (bit0 a))+bit0 a :=
  by 
    simp [bit1, add_smul, smul_add]

@[simp]
theorem bit1_smul_bit1 : bit1 r • bit1 a = (r • bit0 (bit1 a))+bit1 a :=
  by 
    simp only [bit0, bit1, add_smul, smul_add, one_smul]
    abel

end 

variable(R A)

/--
The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def LinearMap : R →ₗ[R] A :=
  { algebraMap R A with
    map_smul' :=
      fun x y =>
        by 
          simp [Algebra.smul_def] }

@[simp]
theorem linear_map_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r :=
  rfl

theorem coe_linear_map : «expr⇑ » (Algebra.linearMap R A) = algebraMap R A :=
  rfl

instance id : Algebra R R :=
  (RingHom.id R).toAlgebra

variable{R A}

namespace id

@[simp]
theorem map_eq_id : algebraMap R R = RingHom.id _ :=
  rfl

theorem map_eq_self (x : R) : algebraMap R R x = x :=
  rfl

@[simp]
theorem smul_eq_mul (x y : R) : x • y = x*y :=
  rfl

end id

section Prod

variable(R A B)

instance  : Algebra R (A × B) :=
  { Prod.module, RingHom.prod (algebraMap R A) (algebraMap R B) with
    commutes' :=
      by 
        rintro r ⟨a, b⟩
        dsimp 
        rw [commutes r a, commutes r b],
    smul_def' :=
      by 
        rintro r ⟨a, b⟩
        dsimp 
        rw [smul_def r a, smul_def r b] }

variable{R A B}

@[simp]
theorem algebra_map_prod_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl

end Prod

/-- Algebra over a subsemiring. This builds upon `subsemiring.module`. -/
instance of_subsemiring (S : Subsemiring R) : Algebra S A :=
  { (algebraMap R A).comp S.subtype with smul := · • ·, commutes' := fun r x => Algebra.commutes r x,
    smul_def' := fun r x => Algebra.smul_def r x }

/-- Algebra over a subring. This builds upon `subring.module`. -/
instance of_subring {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subring R) : Algebra S A :=
  { Algebra.ofSubsemiring S.to_subsemiring, (algebraMap R A).comp S.subtype with smul := · • · }

theorem algebra_map_of_subring {R : Type _} [CommRingₓ R] (S : Subring R) :
  (algebraMap S R : S →+* R) = Subring.subtype S :=
  rfl

theorem coe_algebra_map_of_subring {R : Type _} [CommRingₓ R] (S : Subring R) :
  (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebra_map_of_subring_apply {R : Type _} [CommRingₓ R] (S : Subring R) (x : S) : algebraMap S R x = x :=
  rfl

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebra_map_submonoid (S : Type _) [Semiringₓ S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  Submonoid.map (algebraMap R S : R →* S) M

theorem mem_algebra_map_submonoid_of_mem [Algebra R S] {M : Submonoid R} (x : M) :
  algebraMap R S x ∈ algebra_map_submonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2

end Semiringₓ

section Ringₓ

variable[CommRingₓ R]

variable(R)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure.
See note [reducible non-instances]. -/
@[reducible]
def semiring_to_ring [Semiringₓ A] [Algebra R A] : Ringₓ A :=
  { Module.addCommMonoidToAddCommGroup R, (inferInstance : Semiringₓ A) with  }

variable{R}

theorem mul_sub_algebra_map_commutes [Ringₓ A] [Algebra R A] (x : A) (r : R) :
  (x*x - algebraMap R A r) = (x - algebraMap R A r)*x :=
  by 
    rw [mul_sub, ←commutes, sub_mul]

theorem mul_sub_algebra_map_pow_commutes [Ringₓ A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
  (x*(x - algebraMap R A r) ^ n) = ((x - algebraMap R A r) ^ n)*x :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      rw [pow_succₓ, ←mul_assocₓ, mul_sub_algebra_map_commutes, mul_assocₓ, ih, ←mul_assocₓ]

end Ringₓ

end Algebra

namespace NoZeroSmulDivisors

variable{R A : Type _}

open Algebra

section Ringₓ

variable[CommRingₓ R]

/-- If `algebra_map R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `injective (algebra_map R A)` typeclass.
-/
theorem of_algebra_map_injective [Semiringₓ A] [Algebra R A] [NoZeroDivisors A]
  (h : Function.Injective (algebraMap R A)) : NoZeroSmulDivisors R A :=
  ⟨fun c x hcx => (mul_eq_zero.mp ((smul_def c x).symm.trans hcx)).imp_left ((algebraMap R A).injective_iff.mp h _)⟩

variable(R A)

-- error in Algebra.Algebra.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem algebra_map_injective
[ring A]
[nontrivial A]
[algebra R A]
[no_zero_smul_divisors R A] : function.injective (algebra_map R A) :=
suffices function.injective (λ c : R, «expr • »(c, (1 : A))), by { convert [] [expr this] [],
  ext [] [] [],
  rw ["[", expr algebra.smul_def, ",", expr mul_one, "]"] [] },
smul_left_injective R one_ne_zero

variable{R A}

theorem iff_algebra_map_injective [Ringₓ A] [IsDomain A] [Algebra R A] :
  NoZeroSmulDivisors R A ↔ Function.Injective (algebraMap R A) :=
  ⟨@NoZeroSmulDivisors.algebra_map_injective R A _ _ _ _, NoZeroSmulDivisors.of_algebra_map_injective⟩

end Ringₓ

section Field

variable[Field R][Semiringₓ A][Algebra R A]

instance (priority := 100)algebra.no_zero_smul_divisors [Nontrivial A] [NoZeroDivisors A] : NoZeroSmulDivisors R A :=
  NoZeroSmulDivisors.of_algebra_map_injective (algebraMap R A).Injective

end Field

end NoZeroSmulDivisors

namespace MulOpposite

variable{R A : Type _}[CommSemiringₓ R][Semiringₓ A][Algebra R A]

instance  : Algebra R («expr ᵐᵒᵖ» A) :=
  { MulOpposite.hasScalar A R with toRingHom := (algebraMap R A).toOpposite$ fun x y => Algebra.commutes _ _,
    smul_def' :=
      fun c x =>
        unop_injective$
          by 
            dsimp 
            simp only [op_mul, Algebra.smul_def, Algebra.commutes, op_unop],
    commutes' :=
      fun r =>
        MulOpposite.rec$
          fun x =>
            by 
              dsimp <;> simp only [←op_mul, Algebra.commutes] }

@[simp]
theorem algebra_map_apply (c : R) : algebraMap R («expr ᵐᵒᵖ» A) c = op (algebraMap R A c) :=
  rfl

end MulOpposite

namespace Module

variable(R : Type u)(M : Type v)[CommSemiringₓ R][AddCommMonoidₓ M][Module R M]

instance  : Algebra R (Module.End R M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

theorem algebra_map_End_eq_smul_id (a : R) : (algebraMap R (End R M)) a = a • LinearMap.id :=
  rfl

@[simp]
theorem algebra_map_End_apply (a : R) (m : M) : (algebraMap R (End R M)) a m = a • m :=
  rfl

@[simp]
theorem ker_algebra_map_End (K : Type u) (V : Type v) [Field K] [AddCommGroupₓ V] [Module K V] (a : K) (ha : a ≠ 0) :
  ((algebraMap K (End K V)) a).ker = ⊥ :=
  LinearMap.ker_smul _ _ ha

end Module

/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_inhabited_instance]
structure
  AlgHom(R :
    Type u)(A : Type v)(B : Type w)[CommSemiringₓ R][Semiringₓ A][Semiringₓ B][Algebra R A][Algebra R B] extends
  RingHom A B where 
  commutes' : ∀ (r : R), to_fun (algebraMap R A r) = algebraMap R B r

run_cmd 
  tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

infixr:25 " →ₐ " => AlgHom _

notation:25 A " →ₐ[" R "] " B => AlgHom R A B

namespace AlgHom

variable{R : Type u}{A : Type v}{B : Type w}{C : Type u₁}{D : Type v₁}

section Semiringₓ

variable[CommSemiringₓ R][Semiringₓ A][Semiringₓ B][Semiringₓ C][Semiringₓ D]

variable[Algebra R A][Algebra R B][Algebra R C][Algebra R D]

instance  : CoeFun (A →ₐ[R] B) fun _ => A → B :=
  ⟨AlgHom.toFun⟩

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : A →ₐ[R] B) : f.to_fun = f :=
  rfl

instance coe_ring_hom : Coe (A →ₐ[R] B) (A →+* B) :=
  ⟨AlgHom.toRingHom⟩

instance coe_monoid_hom : Coe (A →ₐ[R] B) (A →* B) :=
  ⟨fun f => «expr↑ » (f : A →+* B)⟩

instance coe_add_monoid_hom : Coe (A →ₐ[R] B) (A →+ B) :=
  ⟨fun f => «expr↑ » (f : A →+* B)⟩

@[simp, normCast]
theorem coe_mk {f : A → B} h₁ h₂ h₃ h₄ h₅ : «expr⇑ » (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  rfl

@[simp]
theorem to_ring_hom_eq_coe (f : A →ₐ[R] B) : f.to_ring_hom = f :=
  rfl

@[simp, normCast]
theorem coe_to_ring_hom (f : A →ₐ[R] B) : «expr⇑ » (f : A →+* B) = f :=
  rfl

@[normCast]
theorem coe_to_monoid_hom (f : A →ₐ[R] B) : «expr⇑ » (f : A →* B) = f :=
  rfl

@[normCast]
theorem coe_to_add_monoid_hom (f : A →ₐ[R] B) : «expr⇑ » (f : A →+ B) = f :=
  rfl

variable(φ : A →ₐ[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) coeFn :=
  by 
    intro φ₁ φ₂ H 
    cases φ₁ 
    cases φ₂ 
    congr 
    exact H

theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  coe_fn_injective.eq_iff

theorem coe_ring_hom_injective : Function.Injective (coeₓ : (A →ₐ[R] B) → A →+* B) :=
  fun φ₁ φ₂ H => coe_fn_injective$ show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_argₓ _ H

theorem coe_monoid_hom_injective : Function.Injective (coeₓ : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoid_hom_injective.comp coe_ring_hom_injective

theorem coe_add_monoid_hom_injective : Function.Injective (coeₓ : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_add_monoid_hom_injective.comp coe_ring_hom_injective

protected theorem congr_funₓ {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  H ▸ rfl

protected theorem congr_argₓ (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  h ▸ rfl

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  coe_fn_injective$ funext H

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  ⟨AlgHom.congr_fun, ext⟩

@[simp]
theorem mk_coe {f : A →ₐ[R] B} h₁ h₂ h₃ h₄ h₅ : (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  ext$ fun _ => rfl

@[simp]
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r

theorem comp_algebra_map : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext$ φ.commutes

@[simp]
theorem map_add (r s : A) : φ (r+s) = φ r+φ s :=
  φ.to_ring_hom.map_add r s

@[simp]
theorem map_zero : φ 0 = 0 :=
  φ.to_ring_hom.map_zero

@[simp]
theorem map_mul x y : φ (x*y) = φ x*φ y :=
  φ.to_ring_hom.map_mul x y

@[simp]
theorem map_one : φ 1 = 1 :=
  φ.to_ring_hom.map_one

@[simp]
theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  by 
    simp only [Algebra.smul_def, map_mul, commutes]

@[simp]
theorem map_pow (x : A) (n : ℕ) : φ (x ^ n) = φ x ^ n :=
  φ.to_ring_hom.map_pow x n

theorem map_sum {ι : Type _} (f : ι → A) (s : Finset ι) : φ (∑x in s, f x) = ∑x in s, φ (f x) :=
  φ.to_ring_hom.map_sum f s

theorem map_finsupp_sum {α : Type _} [HasZero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.sum g) = f.sum fun i a => φ (g i a) :=
  φ.map_sum _ _

@[simp]
theorem map_nat_cast (n : ℕ) : φ n = n :=
  φ.to_ring_hom.map_nat_cast n

@[simp]
theorem map_bit0 x : φ (bit0 x) = bit0 (φ x) :=
  φ.to_ring_hom.map_bit0 x

@[simp]
theorem map_bit1 x : φ (bit1 x) = bit1 (φ x) :=
  φ.to_ring_hom.map_bit1 x

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with toFun := f,
    commutes' :=
      fun c =>
        by 
          simp only [Algebra.algebra_map_eq_smul_one, h, f.map_one] }

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : «expr⇑ » (mk' f h) = f :=
  rfl

section 

variable(R A)

/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }

@[simp]
theorem coe_id : «expr⇑ » (AlgHom.id R A) = id :=
  rfl

@[simp]
theorem id_to_ring_hom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl

end 

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl

-- error in Algebra.Algebra.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : «expr →ₐ[ ] »(B, R, C)) (φ₂ : «expr →ₐ[ ] »(A, R, B)) : «expr →ₐ[ ] »(A, R, C) :=
{ commutes' := λ r : R, by rw ["[", "<-", expr φ₁.commutes, ",", "<-", expr φ₂.commutes, "]"] []; refl,
  ..φ₁.to_ring_hom.comp «expr↑ »(φ₂) }

@[simp]
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : «expr⇑ » (φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

theorem comp_to_ring_hom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
  «expr⇑ » (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp («expr↑ » φ₂) :=
  rfl

@[simp]
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  ext$ fun x => rfl

@[simp]
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  ext$ fun x => rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext$ fun x => rfl

/-- R-Alg ⥤ R-Mod -/
def to_linear_map : A →ₗ[R] B :=
  { toFun := φ, map_add' := φ.map_add, map_smul' := φ.map_smul }

@[simp]
theorem to_linear_map_apply (p : A) : φ.to_linear_map p = φ p :=
  rfl

theorem to_linear_map_injective : Function.Injective (to_linear_map : _ → A →ₗ[R] B) :=
  fun φ₁ φ₂ h => ext$ LinearMap.congr_fun h

@[simp]
theorem comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).toLinearMap = g.to_linear_map.comp f.to_linear_map :=
  rfl

@[simp]
theorem to_linear_map_id : to_linear_map (AlgHom.id R A) = LinearMap.id :=
  LinearMap.ext$ fun _ => rfl

/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def of_linear_map (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x*y) = f x*f y) : A →ₐ[R] B :=
  { f.to_add_monoid_hom with toFun := f, map_one' := map_one, map_mul' := map_mul,
    commutes' :=
      fun c =>
        by 
          simp only [Algebra.algebra_map_eq_smul_one, f.map_smul, map_one] }

@[simp]
theorem of_linear_map_to_linear_map map_one map_mul : of_linear_map φ.to_linear_map map_one map_mul = φ :=
  by 
    ext 
    rfl

@[simp]
theorem to_linear_map_of_linear_map (f : A →ₗ[R] B) map_one map_mul :
  to_linear_map (of_linear_map f map_one map_mul) = f :=
  by 
    ext 
    rfl

@[simp]
theorem of_linear_map_id map_one map_mul : of_linear_map LinearMap.id map_one map_mul = AlgHom.id R A :=
  ext$ fun _ => rfl

theorem map_list_prod (s : List A) : φ s.prod = (s.map φ).Prod :=
  φ.to_ring_hom.map_list_prod s

section Prod

/-- First projection as `alg_hom`. -/
def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun r => rfl }

/-- Second projection as `alg_hom`. -/
def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun r => rfl }

end Prod

theorem algebra_map_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) : algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm

end Semiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R][CommSemiringₓ A][CommSemiringₓ B]

variable[Algebra R A][Algebra R B](φ : A →ₐ[R] B)

theorem map_multiset_prod (s : Multiset A) : φ s.prod = (s.map φ).Prod :=
  φ.to_ring_hom.map_multiset_prod s

theorem map_prod {ι : Type _} (f : ι → A) (s : Finset ι) : φ (∏x in s, f x) = ∏x in s, φ (f x) :=
  φ.to_ring_hom.map_prod f s

theorem map_finsupp_prod {α : Type _} [HasZero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.prod g) = f.prod fun i a => φ (g i a) :=
  φ.map_prod _ _

end CommSemiringₓ

section Ringₓ

variable[CommSemiringₓ R][Ringₓ A][Ringₓ B]

variable[Algebra R A][Algebra R B](φ : A →ₐ[R] B)

@[simp]
theorem map_neg x : φ (-x) = -φ x :=
  φ.to_ring_hom.map_neg x

@[simp]
theorem map_sub x y : φ (x - y) = φ x - φ y :=
  φ.to_ring_hom.map_sub x y

@[simp]
theorem map_int_cast (n : ℤ) : φ n = n :=
  φ.to_ring_hom.map_int_cast n

end Ringₓ

section DivisionRing

variable[CommRingₓ R][DivisionRing A][DivisionRing B]

variable[Algebra R A][Algebra R B](φ : A →ₐ[R] B)

@[simp]
theorem map_inv x : φ (x⁻¹) = φ x⁻¹ :=
  φ.to_ring_hom.map_inv x

@[simp]
theorem map_div x y : φ (x / y) = φ x / φ y :=
  φ.to_ring_hom.map_div x y

end DivisionRing

theorem injective_iff {R A B : Type _} [CommSemiringₓ R] [Ringₓ A] [Semiringₓ B] [Algebra R A] [Algebra R B]
  (f : A →ₐ[R] B) : Function.Injective f ↔ ∀ x, f x = 0 → x = 0 :=
  RingHom.injective_iff (f : A →+* B)

end AlgHom

@[simp]
theorem Rat.smul_one_eq_coe {A : Type _} [DivisionRing A] [Algebra ℚ A] (m : ℚ) : m • (1 : A) = «expr↑ » m :=
  by 
    rw [Algebra.smul_def, mul_oneₓ, RingHom.eq_rat_cast]

/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure
  AlgEquiv(R :
    Type u)(A : Type v)(B : Type w)[CommSemiringₓ R][Semiringₓ A][Semiringₓ B][Algebra R A][Algebra R B] extends
  A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where 
  commutes' : ∀ (r : R), to_fun (algebraMap R A r) = algebraMap R B r

attribute [nolint doc_blame] AlgEquiv.toRingEquiv

attribute [nolint doc_blame] AlgEquiv.toEquiv

attribute [nolint doc_blame] AlgEquiv.toAddEquiv

attribute [nolint doc_blame] AlgEquiv.toMulEquiv

notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

namespace AlgEquiv

variable{R : Type u}{A₁ : Type v}{A₂ : Type w}{A₃ : Type u₁}

section Semiringₓ

variable[CommSemiringₓ R][Semiringₓ A₁][Semiringₓ A₂][Semiringₓ A₃]

variable[Algebra R A₁][Algebra R A₂][Algebra R A₃]

variable(e : A₁ ≃ₐ[R] A₂)

instance  : CoeFun (A₁ ≃ₐ[R] A₂) fun _ => A₁ → A₂ :=
  ⟨AlgEquiv.toFun⟩

-- error in Algebra.Algebra.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[ext #[]] theorem ext {f g : «expr ≃ₐ[ ] »(A₁, R, A₂)} (h : ∀ a, «expr = »(f a, g a)) : «expr = »(f, g) :=
begin
  have [ident h₁] [":", expr «expr = »(f.to_equiv, g.to_equiv)] [":=", expr equiv.ext h],
  cases [expr f] [],
  cases [expr g] [],
  congr,
  { exact [expr funext h] },
  { exact [expr congr_arg equiv.inv_fun h₁] }
end

protected theorem congr_argₓ {f : A₁ ≃ₐ[R] A₂} : ∀ {x x' : A₁}, x = x' → f x = f x'
| _, _, rfl => rfl

protected theorem congr_funₓ {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  h ▸ rfl

theorem ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, ext⟩

theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  by 
    intro f g w 
    ext 
    exact congr_funₓ w a

instance has_coe_to_ring_equiv : Coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) :=
  ⟨AlgEquiv.toRingEquiv⟩

@[simp]
theorem coe_mk {to_fun inv_fun left_inv right_inv map_mul map_add commutes} :
  «expr⇑ » (⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = to_fun :=
  rfl

@[simp]
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) e' h₁ h₂ h₃ h₄ h₅ : (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext$ fun _ => rfl

@[simp]
theorem to_fun_eq_coe (e : A₁ ≃ₐ[R] A₂) : e.to_fun = e :=
  rfl

@[simp]
theorem to_ring_equiv_eq_coe : e.to_ring_equiv = e :=
  rfl

@[simp, normCast]
theorem coe_ring_equiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e :=
  rfl

theorem coe_ring_equiv' : (e.to_ring_equiv : A₁ → A₂) = e :=
  rfl

theorem coe_ring_equiv_injective : Function.Injective (coeₓ : (A₁ ≃ₐ[R] A₂) → A₁ ≃+* A₂) :=
  fun e₁ e₂ h => ext$ RingEquiv.congr_fun h

@[simp]
theorem map_add : ∀ x y, e (x+y) = e x+e y :=
  e.to_add_equiv.map_add

@[simp]
theorem map_zero : e 0 = 0 :=
  e.to_add_equiv.map_zero

@[simp]
theorem map_mul : ∀ x y, e (x*y) = e x*e y :=
  e.to_mul_equiv.map_mul

@[simp]
theorem map_one : e 1 = 1 :=
  e.to_mul_equiv.map_one

@[simp]
theorem commutes : ∀ (r : R), e (algebraMap R A₁ r) = algebraMap R A₂ r :=
  e.commutes'

theorem map_sum {ι : Type _} (f : ι → A₁) (s : Finset ι) : e (∑x in s, f x) = ∑x in s, e (f x) :=
  e.to_add_equiv.map_sum f s

theorem map_finsupp_sum {α : Type _} [HasZero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.sum g) = f.sum fun i b => e (g i b) :=
  e.map_sum _ _

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `has_coe_to_alg_hom` instance. -/
def to_alg_hom : A₁ →ₐ[R] A₂ :=
  { e with map_one' := e.map_one, map_zero' := e.map_zero }

instance has_coe_to_alg_hom : Coe (A₁ ≃ₐ[R] A₂) (A₁ →ₐ[R] A₂) :=
  ⟨to_alg_hom⟩

@[simp]
theorem to_alg_hom_eq_coe : e.to_alg_hom = e :=
  rfl

@[simp, normCast]
theorem coe_alg_hom : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
  rfl

theorem coe_alg_hom_injective : Function.Injective (coeₓ : (A₁ ≃ₐ[R] A₂) → A₁ →ₐ[R] A₂) :=
  fun e₁ e₂ h => ext$ AlgHom.congr_fun h

/-- The two paths coercion can take to a `ring_hom` are equivalent -/
theorem coe_ring_hom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
  rfl

@[simp]
theorem map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = e x ^ n :=
  e.to_alg_hom.map_pow

theorem injective : Function.Injective e :=
  e.to_equiv.injective

theorem surjective : Function.Surjective e :=
  e.to_equiv.surjective

theorem bijective : Function.Bijective e :=
  e.to_equiv.bijective

instance  : HasOne (A₁ ≃ₐ[R] A₁) :=
  ⟨{ (1 : A₁ ≃+* A₁) with commutes' := fun r => rfl }⟩

instance  : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨1⟩

/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R] A₁ :=
  1

@[simp]
theorem refl_to_alg_hom : «expr↑ » (refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ :=
  rfl

@[simp]
theorem coe_refl : «expr⇑ » (refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.to_ring_equiv.symm with
    commutes' :=
      fun r =>
        by 
          rw [←e.to_ring_equiv.symm_apply_apply (algebraMap R A₁ r)]
          congr 
          change _ = e _ 
          rw [e.commutes] }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symmApply)

@[simp]
theorem inv_fun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.inv_fun = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e :=
  by 
    ext 
    rfl

theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) :=
  Equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) f h₁ h₂ h₃ h₄ h₅ : (⟨f, e, h₁, h₂, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
  symm_bijective.Injective$ ext$ fun x => rfl

@[simp]
theorem symm_mk f f' h₁ h₂ h₃ h₄ h₅ :
  (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
    { (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm with toFun := f', invFun := f } :=
  rfl

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.to_ring_equiv.trans e₂.to_ring_equiv with
    commutes' :=
      fun r =>
        show e₂.to_fun (e₁.to_fun _) = _ by 
          rw [e₁.commutes', e₂.commutes'] }

@[simp]
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.to_equiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.to_equiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coeTransₓ (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : «expr⇑ » (e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ →ₐ[R] A₂) («expr↑ » e.symm) = AlgHom.id R A₂ :=
  by 
    ext 
    simp 

@[simp]
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp («expr↑ » e.symm) (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ :=
  by 
    ext 
    simp 

theorem left_inverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem right_inverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrow_congr {A₁' A₂' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Algebra R A₁'] [Algebra R A₂'] (e₁ : A₁ ≃ₐ[R] A₁')
  (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') :=
  { toFun := fun f => (e₂.to_alg_hom.comp f).comp e₁.symm.to_alg_hom,
    invFun := fun f => (e₂.symm.to_alg_hom.comp f).comp e₁.to_alg_hom,
    left_inv :=
      fun f =>
        by 
          simp only [AlgHom.comp_assoc, to_alg_hom_eq_coe, symm_comp]
          simp only [←AlgHom.comp_assoc, symm_comp, AlgHom.id_comp, AlgHom.comp_id],
    right_inv :=
      fun f =>
        by 
          simp only [AlgHom.comp_assoc, to_alg_hom_eq_coe, comp_symm]
          simp only [←AlgHom.comp_assoc, comp_symm, AlgHom.id_comp, AlgHom.comp_id] }

theorem arrow_congr_comp {A₁' A₂' A₃' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Semiringₓ A₃'] [Algebra R A₁']
  [Algebra R A₂'] [Algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂)
  (g : A₂ →ₐ[R] A₃) : arrow_congr e₁ e₃ (g.comp f) = (arrow_congr e₂ e₃ g).comp (arrow_congr e₁ e₂ f) :=
  by 
    ext 
    simp only [arrow_congr, Equiv.coe_fn_mk, AlgHom.comp_apply]
    congr 
    exact (e₂.symm_apply_apply _).symm

@[simp]
theorem arrow_congr_refl : arrow_congr AlgEquiv.refl AlgEquiv.refl = Equiv.refl (A₁ →ₐ[R] A₂) :=
  by 
    ext 
    rfl

@[simp]
theorem arrow_congr_trans {A₁' A₂' A₃' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Semiringₓ A₃'] [Algebra R A₁']
  [Algebra R A₂'] [Algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂') (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
  by 
    ext 
    rfl

@[simp]
theorem arrow_congr_symm {A₁' A₂' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Algebra R A₁'] [Algebra R A₂']
  (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
  by 
    ext 
    rfl

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂) (h₂ : g.comp f = AlgHom.id R A₁) :
  A₁ ≃ₐ[R] A₂ :=
  { f with toFun := f, invFun := g, left_inv := AlgHom.ext_iff.1 h₂, right_inv := AlgHom.ext_iff.1 h₁ }

theorem coe_alg_hom_of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) h₁ h₂ : «expr↑ » (of_alg_hom f g h₁ h₂) = f :=
  AlgHom.ext$ fun _ => rfl

@[simp]
theorem of_alg_hom_coe_alg_hom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) h₁ h₂ : of_alg_hom («expr↑ » f) g h₁ h₂ = f :=
  ext$ fun _ => rfl

theorem of_alg_hom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) h₁ h₂ :
  (of_alg_hom f g h₁ h₂).symm = of_alg_hom g f h₂ h₁ :=
  rfl

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def of_bijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with  }

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def to_linear_equiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
  { e with toFun := e,
    map_smul' :=
      fun r x =>
        by 
          simp [Algebra.smul_def],
    invFun := e.symm }

@[simp]
theorem to_linear_equiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl

@[simp]
theorem to_linear_equiv_symm (e : A₁ ≃ₐ[R] A₂) : e.to_linear_equiv.symm = e.symm.to_linear_equiv :=
  rfl

@[simp]
theorem to_linear_equiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  (e₁.trans e₂).toLinearEquiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv :=
  rfl

theorem to_linear_equiv_injective : Function.Injective (to_linear_equiv : _ → A₁ ≃ₗ[R] A₂) :=
  fun e₁ e₂ h => ext$ LinearEquiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def to_linear_map : A₁ →ₗ[R] A₂ :=
  e.to_alg_hom.to_linear_map

@[simp]
theorem to_alg_hom_to_linear_map : (e : A₁ →ₐ[R] A₂).toLinearMap = e.to_linear_map :=
  rfl

@[simp]
theorem to_linear_equiv_to_linear_map : e.to_linear_equiv.to_linear_map = e.to_linear_map :=
  rfl

@[simp]
theorem to_linear_map_apply (x : A₁) : e.to_linear_map x = e x :=
  rfl

theorem to_linear_map_injective : Function.Injective (to_linear_map : _ → A₁ →ₗ[R] A₂) :=
  fun e₁ e₂ h => ext$ LinearMap.congr_fun h

@[simp]
theorem trans_to_linear_map (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
  (f.trans g).toLinearMap = g.to_linear_map.comp f.to_linear_map :=
  rfl

section OfLinearEquiv

variable(l :
    A₁ ≃ₗ[R]
      A₂)(map_mul : ∀ (x y : A₁), l (x*y) = l x*l y)(commutes : ∀ (r : R), l (algebraMap R A₁ r) = algebraMap R A₂ r)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and action of scalars.
-/
@[simps apply]
def of_linear_equiv : A₁ ≃ₐ[R] A₂ :=
  { l with toFun := l, invFun := l.symm, map_mul' := map_mul, commutes' := commutes }

@[simp]
theorem of_linear_equiv_symm :
  (of_linear_equiv l map_mul commutes).symm =
    of_linear_equiv l.symm (of_linear_equiv l map_mul commutes).symm.map_mul
      (of_linear_equiv l map_mul commutes).symm.commutes :=
  rfl

@[simp]
theorem of_linear_equiv_to_linear_equiv map_mul commutes : of_linear_equiv e.to_linear_equiv map_mul commutes = e :=
  by 
    ext 
    rfl

@[simp]
theorem to_linear_equiv_of_linear_equiv : to_linear_equiv (of_linear_equiv l map_mul commutes) = l :=
  by 
    ext 
    rfl

end OfLinearEquiv

instance aut : Groupₓ (A₁ ≃ₐ[R] A₁) :=
  { mul := fun ϕ ψ => ψ.trans ϕ, mul_assoc := fun ϕ ψ χ => rfl, one := 1,
    one_mul :=
      fun ϕ =>
        by 
          ext 
          rfl,
    mul_one :=
      fun ϕ =>
        by 
          ext 
          rfl,
    inv := symm,
    mul_left_inv :=
      fun ϕ =>
        by 
          ext 
          exact symm_apply_apply ϕ a }

@[simp]
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁*e₂) x = e₁ (e₂ x) :=
  rfl

/-- An algebra isomorphism induces a group isomorphism between automorphism groups -/
@[simps apply]
def aut_congr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ :=
  { toFun := fun ψ => ϕ.symm.trans (ψ.trans ϕ), invFun := fun ψ => ϕ.trans (ψ.trans ϕ.symm),
    left_inv :=
      fun ψ =>
        by 
          ext 
          simpRw [trans_apply, symm_apply_apply],
    right_inv :=
      fun ψ =>
        by 
          ext 
          simpRw [trans_apply, apply_symm_apply],
    map_mul' :=
      fun ψ χ =>
        by 
          ext 
          simp only [mul_apply, trans_apply, symm_apply_apply] }

@[simp]
theorem aut_congr_refl : aut_congr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) :=
  by 
    ext 
    rfl

@[simp]
theorem aut_congr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (aut_congr ϕ).symm = aut_congr ϕ.symm :=
  rfl

@[simp]
theorem aut_congr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
  (aut_congr ϕ).trans (aut_congr ψ) = aut_congr (ϕ.trans ψ) :=
  rfl

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_mul_semiring_action : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ :=
  { smul := ·$ ·, smul_zero := AlgEquiv.map_zero, smul_add := AlgEquiv.map_add, smul_one := AlgEquiv.map_one,
    smul_mul := AlgEquiv.map_mul, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }

@[simp]
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl

instance apply_has_faithful_scalar : HasFaithfulScalar (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨fun _ _ => AlgEquiv.ext⟩

instance apply_smul_comm_class : SmulCommClass R (A₁ ≃ₐ[R] A₁) A₁ :=
  { smul_comm := fun r e a => (e.to_linear_equiv.map_smul r a).symm }

instance apply_smul_comm_class' : SmulCommClass (A₁ ≃ₐ[R] A₁) R A₁ :=
  { smul_comm := fun e r a => e.to_linear_equiv.map_smul r a }

@[simp]
theorem algebra_map_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} : algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h =>
      by 
        simpa using e.symm.to_alg_hom.algebra_map_eq_apply h,
    fun h => e.to_alg_hom.algebra_map_eq_apply h⟩

end Semiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R][CommSemiringₓ A₁][CommSemiringₓ A₂]

variable[Algebra R A₁][Algebra R A₂](e : A₁ ≃ₐ[R] A₂)

theorem map_prod {ι : Type _} (f : ι → A₁) (s : Finset ι) : e (∏x in s, f x) = ∏x in s, e (f x) :=
  e.to_alg_hom.map_prod f s

theorem map_finsupp_prod {α : Type _} [HasZero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.prod g) = f.prod fun i a => e (g i a) :=
  e.to_alg_hom.map_finsupp_prod f g

end CommSemiringₓ

section Ringₓ

variable[CommRingₓ R][Ringₓ A₁][Ringₓ A₂]

variable[Algebra R A₁][Algebra R A₂](e : A₁ ≃ₐ[R] A₂)

@[simp]
theorem map_neg x : e (-x) = -e x :=
  e.to_alg_hom.map_neg x

@[simp]
theorem map_sub x y : e (x - y) = e x - e y :=
  e.to_alg_hom.map_sub x y

end Ringₓ

section DivisionRing

variable[CommRingₓ R][DivisionRing A₁][DivisionRing A₂]

variable[Algebra R A₁][Algebra R A₂](e : A₁ ≃ₐ[R] A₂)

@[simp]
theorem map_inv x : e (x⁻¹) = e x⁻¹ :=
  e.to_alg_hom.map_inv x

@[simp]
theorem map_div x y : e (x / y) = e x / e y :=
  e.to_alg_hom.map_div x y

end DivisionRing

end AlgEquiv

namespace MulSemiringAction

variable{M G : Type _}(R A : Type _)[CommSemiringₓ R][Semiringₓ A][Algebra R A]

section 

variable[Monoidₓ M][MulSemiringAction M A][SmulCommClass M R A]

/-- Each element of the monoid defines a algebra homomorphism.

This is a stronger version of `mul_semiring_action.to_ring_hom` and
`distrib_mul_action.to_linear_map`. -/
@[simps]
def to_alg_hom (m : M) : A →ₐ[R] A :=
  AlgHom.mk' (MulSemiringAction.toRingHom _ _ m) (smul_comm _)

theorem to_alg_hom_injective [HasFaithfulScalar M A] :
  Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) :=
  fun m₁ m₂ h => eq_of_smul_eq_smul$ fun r => AlgHom.ext_iff.1 h r

end 

section 

variable[Groupₓ G][MulSemiringAction G A][SmulCommClass G R A]

/-- Each element of the group defines a algebra equivalence.

This is a stronger version of `mul_semiring_action.to_ring_equiv` and
`distrib_mul_action.to_linear_equiv`. -/
@[simps]
def to_alg_equiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with  }

theorem to_alg_equiv_injective [HasFaithfulScalar G A] :
  Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) :=
  fun m₁ m₂ h => eq_of_smul_eq_smul$ fun r => AlgEquiv.ext_iff.1 h r

end 

end MulSemiringAction

section Nat

variable{R : Type _}[Semiringₓ R]

/-- Semiring ⥤ ℕ-Alg -/
instance (priority := 99)algebraNat : Algebra ℕ R :=
  { commutes' := Nat.cast_commute, smul_def' := fun _ _ => nsmul_eq_mul _ _, toRingHom := Nat.castRingHom R }

instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q =>
      by 
        ext 
        simp ⟩

end Nat

namespace RingHom

variable{R S : Type _}

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def to_nat_alg_hom [Semiringₓ R] [Semiringₓ S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with toFun := f,
    commutes' :=
      fun n =>
        by 
          simp  }

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def to_int_alg_hom [Ringₓ R] [Ringₓ S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with
    commutes' :=
      fun n =>
        by 
          simp  }

@[simp]
theorem map_rat_algebra_map [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) (r : ℚ) :
  f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elimₓ (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. -/
def to_rat_alg_hom [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebra_map }

end RingHom

namespace Rat

instance algebra_rat {α} [DivisionRing α] [CharZero α] : Algebra ℚ α :=
  (Rat.castHom α).toAlgebra'$ fun r x => r.cast_commute x

@[simp]
theorem algebra_map_rat_rat : algebraMap ℚ ℚ = RingHom.id ℚ :=
  Subsingleton.elimₓ _ _

theorem algebra_rat_subsingleton {α} [Semiringₓ α] : Subsingleton (Algebra ℚ α) :=
  ⟨fun x y => Algebra.algebra_ext x y$ RingHom.congr_fun$ Subsingleton.elimₓ _ _⟩

end Rat

namespace CharZero

variable{R : Type _}(S : Type _)[CommSemiringₓ R][Semiringₓ S][Algebra R S]

theorem of_algebra [CharZero S] : CharZero R :=
  ⟨by 
      suffices  : Function.Injective (algebraMap R S ∘ coeₓ)
      ·
        exact this.of_comp 
      convert CharZero.cast_injective 
      ext n 
      rw [Function.comp_app, ←(algebraMap ℕ _).eq_nat_cast, ←RingHom.comp_apply, RingHom.eq_nat_cast]
      all_goals 
        infer_instance⟩

end CharZero

namespace Algebra

open Module

variable(R : Type u)(A : Type v)

variable[CommSemiringₓ R][Semiringₓ A][Algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def of_id : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }

variable{R}

theorem of_id_apply r : of_id R A r = algebraMap R A r :=
  rfl

end Algebra

section Int

variable(R : Type _)[Ringₓ R]

/-- Ring ⥤ ℤ-Alg -/
instance (priority := 99)algebraInt : Algebra ℤ R :=
  { commutes' := Int.cast_commute, smul_def' := fun _ _ => zsmul_eq_mul _ _, toRingHom := Int.castRingHom R }

variable{R}

instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q =>
      by 
        ext 
        simp ⟩

end Int

/-!
The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

We couldn't set this up back in `algebra.pi_instances` because this file imports it.
-/


namespace Pi

variable{I : Type u}

variable{R : Type _}

variable{f : I → Type v}

variable(x y : ∀ i, f i)(i : I)

variable(I f)

instance Algebra {r : CommSemiringₓ R} [s : ∀ i, Semiringₓ (f i)] [∀ i, Algebra R (f i)] : Algebra R (∀ (i : I), f i) :=
  { (Pi.ringHom fun i => algebraMap R (f i) : R →+* ∀ (i : I), f i) with
    commutes' :=
      fun a f =>
        by 
          ext 
          simp [Algebra.commutes],
    smul_def' :=
      fun a f =>
        by 
          ext 
          simp [Algebra.smul_def] }

@[simp]
theorem algebra_map_apply {r : CommSemiringₓ R} [s : ∀ i, Semiringₓ (f i)] [∀ i, Algebra R (f i)] (a : R) (i : I) :
  algebraMap R (∀ i, f i) a i = algebraMap R (f i) a :=
  rfl

variable{I}(R)(f)

/-- `function.eval` as an `alg_hom`. The name matches `pi.eval_ring_hom`, `pi.eval_monoid_hom`,
etc. -/
@[simps]
def eval_alg_hom {r : CommSemiringₓ R} [∀ i, Semiringₓ (f i)] [∀ i, Algebra R (f i)] (i : I) : (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with toFun := fun f => f i, commutes' := fun r => rfl }

variable(A B : Type _)[CommSemiringₓ R][Semiringₓ B][Algebra R B]

/-- `function.const` as an `alg_hom`. The name matches `pi.const_ring_hom`, `pi.const_monoid_hom`,
etc. -/
@[simps]
def const_alg_hom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with toFun := Function.const _, commutes' := fun r => rfl }

/-- When `R` is commutative and permits an `algebra_map`, `pi.const_ring_hom` is equal to that
map. -/
@[simp]
theorem const_ring_hom_eq_algebra_map : const_ring_hom A R = algebraMap R (A → R) :=
  rfl

@[simp]
theorem const_alg_hom_eq_algebra_of_id : const_alg_hom R A R = Algebra.ofId R (A → R) :=
  rfl

end Pi

section IsScalarTower

variable{R : Type _}[CommSemiringₓ R]

variable(A : Type _)[Semiringₓ A][Algebra R A]

variable{M : Type _}[AddCommMonoidₓ M][Module A M][Module R M][IsScalarTower R A M]

variable{N : Type _}[AddCommMonoidₓ N][Module A N][Module R N][IsScalarTower R A N]

theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m :=
  by 
    rw [←one_smul A m, ←smul_assoc, Algebra.smul_def, mul_oneₓ, one_smul]

@[simp]
theorem algebra_map_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm

variable{A}

instance (priority := 100)IsScalarTower.to_smul_comm_class : SmulCommClass R A M :=
  ⟨fun r a m =>
      by 
        rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ←algebra_compatible_smul]⟩

instance (priority := 100)IsScalarTower.to_smul_comm_class' : SmulCommClass A R M :=
  SmulCommClass.symm _ _ _

theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _

namespace LinearMap

instance coe_is_scalar_tower : Coe (M →ₗ[A] N) (M →ₗ[R] N) :=
  ⟨restrict_scalars R⟩

variable(R){A M N}

@[simp, normCast squash]
theorem coe_restrict_scalars_eq_coe (f : M →ₗ[A] N) : (f.restrict_scalars R : M → N) = f :=
  rfl

@[simp, normCast squash]
theorem coe_coe_is_scalar_tower (f : M →ₗ[A] N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def lto_fun (R : Type u) (M : Type v) (A : Type w) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [CommRingₓ A]
  [Algebra R A] : (M →ₗ[R] A) →ₗ[A] M → A :=
  { toFun := LinearMap.toFun, map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

end LinearMap

end IsScalarTower

/-! TODO: The following lemmas no longer involve `algebra` at all, and could be moved closer
to `algebra/module/submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `linear_algebra/basic.lean`. -/


section Module

open Module

variable(R S M N : Type _)[Semiringₓ R][Semiringₓ S][HasScalar R S]

variable[AddCommMonoidₓ M][Module R M][Module S M][IsScalarTower R S M]

variable[AddCommMonoidₓ N][Module R N][Module S N][IsScalarTower R S N]

variable{S M N}

@[simp]
theorem LinearMap.ker_restrict_scalars (f : M →ₗ[S] N) : (f.restrict_scalars R).ker = f.ker.restrict_scalars R :=
  rfl

end Module

namespace Submodule

variable(R A M : Type _)

variable[CommSemiringₓ R][Semiringₓ A][Algebra R A][AddCommMonoidₓ M]

variable[Module R M][Module A M][IsScalarTower R A M]

/-- If `A` is an `R`-algebra such that the induced morhpsim `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
theorem span_eq_restrict_scalars (X : Set M) (hsur : Function.Surjective (algebraMap R A)) :
  span R X = restrict_scalars R (span A X) :=
  by 
    apply (span_le_restrict_scalars R A X).antisymm fun m hm => _ 
    refine' span_induction hm subset_span (zero_mem _) (fun _ _ => add_mem _) fun a m hm => _ 
    obtain ⟨r, rfl⟩ := hsur a 
    simpa [algebra_map_smul] using smul_mem _ r hm

end Submodule

namespace AlgHom

variable{R : Type u}{A : Type v}{B : Type w}{I : Type _}

variable[CommSemiringₓ R][Semiringₓ A][Semiringₓ B]

variable[Algebra R A][Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
protected def comp_left (f : A →ₐ[R] B) (I : Type _) : (I → A) →ₐ[R] I → B :=
  { f.to_ring_hom.comp_left I with toFun := fun h => f ∘ h,
    commutes' :=
      fun c =>
        by 
          ext 
          exact f.commutes' c }

end AlgHom

