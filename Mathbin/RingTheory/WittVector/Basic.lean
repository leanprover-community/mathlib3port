import Mathbin.Data.MvPolynomial.Counit
import Mathbin.Data.MvPolynomial.Invertible
import Mathbin.RingTheory.WittVector.Defs

/-!
# Witt vectors

This file verifies that the ring operations on `witt_vector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `witt_vector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `witt_vector.ghost_component n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `witt_vector.ghost_map`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `witt_vector.comm_ring`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/


noncomputable section

open MvPolynomial Function

open_locale BigOperators

variable {p : ℕ} {R S T : Type _} [hp : Fact p.prime] [CommRingₓ R] [CommRingₓ S] [CommRingₓ T]

variable {α : Type _} {β : Type _}

local notation "𝕎" => WittVector p

open_locale Witt

namespace WittVector

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `witt_vector.map f`. -/
def map_fun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)

namespace MapFun

theorem injective (f : α → β) (hf : injective f) : injective (map_fun f : 𝕎 α → 𝕎 β) := fun x y h =>
  ext fun n => hf (congr_argₓ (fun x => coeff x n) h : _)

theorem surjective (f : α → β) (hf : surjective f) : surjective (map_fun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.some <| hf <| x.coeff n, by
    ext n
    dsimp [map_fun]
    rw [Classical.some_spec (hf (x.coeff n))]⟩

variable (f : R →+* S) (x y : 𝕎 R)

-- ././Mathport/Syntax/Translate/Basic.lean:794:4: warning: unsupported (TODO): `[tacs]
/-- Auxiliary tactic for showing that `map_fun` respects the ring operations. -/
unsafe def map_fun_tac : tactic Unit :=
  sorry

include hp

theorem zero : map_fun f (0 : 𝕎 R) = 0 := by
  run_tac
    map_fun_tac

theorem one : map_fun f (1 : 𝕎 R) = 1 := by
  run_tac
    map_fun_tac

theorem add : map_fun f (x + y) = map_fun f x + map_fun f y := by
  run_tac
    map_fun_tac

theorem sub : map_fun f (x - y) = map_fun f x - map_fun f y := by
  run_tac
    map_fun_tac

theorem mul : map_fun f (x * y) = map_fun f x * map_fun f y := by
  run_tac
    map_fun_tac

theorem neg : map_fun f (-x) = -map_fun f x := by
  run_tac
    map_fun_tac

end MapFun

end WittVector

section Tactic

setup_tactic_parser

open Tactic

-- ././Mathport/Syntax/Translate/Basic.lean:794:4: warning: unsupported (TODO): `[tacs]
-- ././Mathport/Syntax/Translate/Basic.lean:794:4: warning: unsupported (TODO): `[tacs]
-- ././Mathport/Syntax/Translate/Basic.lean:794:4: warning: unsupported (TODO): `[tacs]
/-- An auxiliary tactic for proving that `ghost_fun` respects the ring operations. -/
unsafe def tactic.interactive.ghost_fun_tac (φ fn : parse parser.pexpr) : tactic Unit := do
  let fn ← to_expr (ppquote.1 (%%ₓfn : Finₓ _ → ℕ → R))
  let quote.1 (Finₓ (%%ₓk) → _ → _) ← infer_type fn
  sorry
  sorry
  to_expr (ppquote.1 (congr_funₓ (congr_argₓ (@peval R _ (%%ₓk)) (witt_structure_int_prop p (%%ₓφ) n)) (%%ₓfn))) >>=
      note `this none
  sorry

end Tactic

namespace WittVector

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `witt_vector.ghost_map`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
private def ghost_fun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)

section GhostFun

include hp

variable (x y : 𝕎 R)

omit hp

@[local simp]
theorem matrix_vec_empty_coeff {R} i j : @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : ℕ → R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩

include hp

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
private theorem ghost_fun_zero : ghost_fun (0 : 𝕎 R) = 0 := by
  ghost_fun_tac 0, «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
private theorem ghost_fun_one : ghost_fun (1 : 𝕎 R) = 1 := by
  ghost_fun_tac 1, «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
private theorem ghost_fun_add : ghost_fun (x + y) = ghost_fun x + ghost_fun y := by
  ghost_fun_tac X 0 + X 1,
    «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
private theorem ghost_fun_sub : ghost_fun (x - y) = ghost_fun x - ghost_fun y := by
  ghost_fun_tac X 0 - X 1,
    «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
private theorem ghost_fun_mul : ghost_fun (x * y) = ghost_fun x * ghost_fun y := by
  ghost_fun_tac X 0 * X 1,
    «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
private theorem ghost_fun_neg : ghost_fun (-x) = -ghost_fun x := by
  ghost_fun_tac -X 0, «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"

end GhostFun

variable (p) (R)

/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `witt_vector.ghost_equiv` we upgrade this to an isomorphism of rings. -/
private def ghost_equiv' [Invertible (p : R)] : 𝕎 R ≃ (ℕ → R) where
  toFun := ghost_fun
  invFun := fun x => (mk p) fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_witt_polynomial_X_in_terms_of_W p R n
    apply_fun aeval x.coeff  at this
    simpa only [aeval_bind₁, aeval_X, ghost_fun, aeval_witt_polynomial]
  right_inv := by
    intro x
    ext n
    have := bind₁_X_in_terms_of_W_witt_polynomial p R n
    apply_fun aeval x  at this
    simpa only [aeval_bind₁, aeval_X, ghost_fun, aeval_witt_polynomial]

include hp

@[local instance]
private def comm_ring_aux₁ : CommRingₓ (𝕎 (MvPolynomial R ℚ)) :=
  (ghost_equiv' p (MvPolynomial R ℚ)).Injective.CommRing ghost_fun ghost_fun_zero ghost_fun_one ghost_fun_add
    ghost_fun_mul ghost_fun_neg ghost_fun_sub

@[local instance]
private def comm_ring_aux₂ : CommRingₓ (𝕎 (MvPolynomial R ℤ)) :=
  (map_fun.injective _ <| map_injective (Int.castRingHom ℚ) Int.cast_injective).CommRing _ (map_fun.zero _)
    (map_fun.one _) (map_fun.add _) (map_fun.mul _) (map_fun.neg _) (map_fun.sub _)

/-- The commutative ring structure on `𝕎 R`. -/
instance : CommRingₓ (𝕎 R) :=
  (map_fun.surjective _ <| counit_surjective _).CommRing (map_fun <| MvPolynomial.counit _) (map_fun.zero _)
    (map_fun.one _) (map_fun.add _) (map_fun.mul _) (map_fun.neg _) (map_fun.sub _)

variable {p R}

/-- `witt_vector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
def map (f : R →+* S) : 𝕎 R →+* 𝕎 S where
  toFun := map_fun f
  map_zero' := map_fun.zero f
  map_one' := map_fun.one f
  map_add' := map_fun.add f
  map_mul' := map_fun.mul f

theorem map_injective (f : R →+* S) (hf : injective f) : injective (map f : 𝕎 R → 𝕎 S) :=
  map_fun.injective f hf

theorem map_surjective (f : R →+* S) (hf : surjective f) : surjective (map f : 𝕎 R → 𝕎 S) :=
  map_fun.surjective f hf

@[simp]
theorem map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) : (map f x).coeff n = f (x.coeff n) :=
  rfl

/-- `witt_vector.ghost_map` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
def ghost_map : 𝕎 R →+* ℕ → R where
  toFun := ghost_fun
  map_zero' := ghost_fun_zero
  map_one' := ghost_fun_one
  map_add' := ghost_fun_add
  map_mul' := ghost_fun_mul

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
def ghost_component (n : ℕ) : 𝕎 R →+* R :=
  (Pi.evalRingHom _ n).comp ghost_map

theorem ghost_component_apply (n : ℕ) (x : 𝕎 R) : ghost_component n x = aeval x.coeff (W_ ℤ n) :=
  rfl

@[simp]
theorem ghost_map_apply (x : 𝕎 R) (n : ℕ) : ghost_map x n = ghost_component n x :=
  rfl

section Invertible

variable (p R) [Invertible (p : R)]

/-- `witt_vector.ghost_map` is a ring isomorphism when `p` is invertible in `R`. -/
def ghost_equiv : 𝕎 R ≃+* (ℕ → R) :=
  { (ghost_map : 𝕎 R →+* ℕ → R), ghost_equiv' p R with }

@[simp]
theorem ghost_equiv_coe : (ghost_equiv p R : 𝕎 R →+* ℕ → R) = ghost_map :=
  rfl

theorem ghost_map.bijective_of_invertible : Function.Bijective (ghost_map : 𝕎 R → ℕ → R) :=
  (ghost_equiv p R).Bijective

end Invertible

/-- `witt_vector.coeff x 0` as a `ring_hom` -/
@[simps]
def constant_coeff : 𝕎 R →+* R where
  toFun := fun x => x.coeff 0
  map_zero' := by
    simp
  map_one' := by
    simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero

instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constant_coeff.domain_nontrivial

end WittVector

