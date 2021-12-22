import Mathbin.Algebra.MonoidAlgebra.Basic

/-!
# Theory of univariate polynomials

This file defines `polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n in p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g`.

## Implementation

Polynomials are defined using `add_monoid_algebra R ℕ`, where `R` is a commutative semiring, but
through a structure to make them irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `add_monoid_algebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `polynomial R` and `add_monoid_algebra R ℕ` is
done through `of_finsupp` and `to_finsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `add_monoid_algebra R ℕ`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `polynomial.to_finsupp_iso`. These should
in general not be used once the basic API for polynomials is constructed.
-/


noncomputable section

/--  `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure Polynomial (R : Type _) [Semiringₓ R] where of_finsupp ::
  toFinsupp : AddMonoidAlgebra R ℕ

open Finsupp AddMonoidAlgebra

open_locale BigOperators

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q : Polynomial R}

theorem forall_iff_forall_finsupp (P : Polynomial R → Prop) : (∀ p, P p) ↔ ∀ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

theorem exists_iff_exists_finsupp (P : Polynomial R → Prop) : (∃ p, P p) ↔ ∃ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

/--  The function version of `monomial`. Use `monomial` instead of this one. -/
irreducible_def monomial_fun (n : ℕ) (a : R) : Polynomial R :=
  ⟨Finsupp.single n a⟩

private irreducible_def add : Polynomial R → Polynomial R → Polynomial R
  | ⟨a⟩, ⟨b⟩ => ⟨a+b⟩

private irreducible_def neg {R : Type u} [Ringₓ R] : Polynomial R → Polynomial R
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : Polynomial R → Polynomial R → Polynomial R
  | ⟨a⟩, ⟨b⟩ => ⟨a*b⟩

instance : HasZero (Polynomial R) :=
  ⟨⟨0⟩⟩

instance : HasOne (Polynomial R) :=
  ⟨monomial_fun 0 (1 : R)⟩

instance : Add (Polynomial R) :=
  ⟨add⟩

instance {R : Type u} [Ringₓ R] : Neg (Polynomial R) :=
  ⟨neg⟩

instance : Mul (Polynomial R) :=
  ⟨mul⟩

instance {S : Type _} [Monoidₓ S] [DistribMulAction S R] : HasScalar S (Polynomial R) :=
  ⟨fun r p => ⟨r • p.to_finsupp⟩⟩

theorem zero_to_finsupp : (⟨0⟩ : Polynomial R) = 0 :=
  rfl

theorem one_to_finsupp : (⟨1⟩ : Polynomial R) = 1 := by
  change (⟨1⟩ : Polynomial R) = monomial_fun 0 (1 : R)
  rw [monomial_fun]
  rfl

theorem add_to_finsupp {a b} : (⟨a⟩+⟨b⟩ : Polynomial R) = ⟨a+b⟩ :=
  show add _ _ = _ by
    rw [add]

theorem neg_to_finsupp {R : Type u} [Ringₓ R] {a} : (-⟨a⟩ : Polynomial R) = ⟨-a⟩ :=
  show neg _ = _ by
    rw [neg]

theorem mul_to_finsupp {a b} : (⟨a⟩*⟨b⟩ : Polynomial R) = ⟨a*b⟩ :=
  show mul _ _ = _ by
    rw [mul]

theorem smul_to_finsupp {S : Type _} [Monoidₓ S] [DistribMulAction S R] {a : S} {b} :
    (a • ⟨b⟩ : Polynomial R) = ⟨a • b⟩ :=
  rfl

theorem _root_.is_smul_regular.polynomial {S : Type _} [Monoidₓ S] [DistribMulAction S R] {a : S}
    (ha : IsSmulRegular R a) : IsSmulRegular (Polynomial R) a
  | ⟨x⟩, ⟨y⟩, h => congr_argₓ _ $ ha.finsupp (Polynomial.of_finsupp.inj h)

instance : Inhabited (Polynomial R) :=
  ⟨0⟩

instance : Semiringₓ (Polynomial R) := by
  refine_struct
      { zero := (0 : Polynomial R), one := 1, mul := ·*·, add := ·+·, nsmul := · • ·, npow := npowRec,
        npow_zero' := fun x => rfl, npow_succ' := fun n x => rfl } <;>
    ·
      repeat'
          rintro ⟨_⟩ <;>
        simp [← zero_to_finsupp, ← one_to_finsupp, add_to_finsupp, mul_to_finsupp, mul_assocₓ, mul_addₓ, add_mulₓ,
            smul_to_finsupp, Nat.succ_eq_one_add] <;>
          abel

instance {S} [Monoidₓ S] [DistribMulAction S R] : DistribMulAction S (Polynomial R) where
  smul := · • ·
  one_smul := by
    rintro ⟨⟩
    simp [smul_to_finsupp]
  mul_smul := by
    rintro _ _ ⟨⟩
    simp [smul_to_finsupp, mul_smul]
  smul_add := by
    rintro _ ⟨⟩ ⟨⟩
    simp [smul_to_finsupp, add_to_finsupp]
  smul_zero := by
    rintro _
    simp [← zero_to_finsupp, smul_to_finsupp]

-- failed to format: format: uncaught backtrack exception
instance
  { S } [ Monoidₓ S ] [ DistribMulAction S R ] [ HasFaithfulScalar S R ] : HasFaithfulScalar S ( Polynomial R )
  where eq_of_smul_eq_smul s₁ s₂ h := eq_of_smul_eq_smul $ fun a : ℕ →₀ R => congr_argₓ to_finsupp ( h ⟨ a ⟩ )

instance {S} [Semiringₓ S] [Module S R] : Module S (Polynomial R) :=
  { Polynomial.distribMulAction with smul := · • ·,
    add_smul := by
      rintro _ _ ⟨⟩
      simp [smul_to_finsupp, add_to_finsupp, add_smul],
    zero_smul := by
      rintro ⟨⟩
      simp [smul_to_finsupp, ← zero_to_finsupp] }

instance {S₁ S₂} [Monoidₓ S₁] [Monoidₓ S₂] [DistribMulAction S₁ R] [DistribMulAction S₂ R] [SmulCommClass S₁ S₂ R] :
    SmulCommClass S₁ S₂ (Polynomial R) :=
  ⟨by
    rintro _ _ ⟨⟩
    simp [smul_to_finsupp, smul_comm]⟩

instance {S₁ S₂} [HasScalar S₁ S₂] [Monoidₓ S₁] [Monoidₓ S₂] [DistribMulAction S₁ R] [DistribMulAction S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ (Polynomial R) :=
  ⟨by
    rintro _ _ ⟨⟩
    simp [smul_to_finsupp]⟩

instance {S} [Monoidₓ S] [DistribMulAction S R] [DistribMulAction (Sᵐᵒᵖ) R] [IsCentralScalar S R] :
    IsCentralScalar S (Polynomial R) :=
  ⟨by
    rintro _ ⟨⟩
    simp [smul_to_finsupp, op_smul_eq_smul]⟩

instance [Subsingleton R] : Unique (Polynomial R) :=
  { Polynomial.inhabited with
    uniq := by
      rintro ⟨x⟩
      change (⟨x⟩ : Polynomial R) = 0
      rw [← zero_to_finsupp]
      simp }

variable (R)

/--  Ring isomorphism between `polynomial R` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps]
def to_finsupp_iso : Polynomial R ≃+* AddMonoidAlgebra R ℕ :=
  { toFun := fun p => p.to_finsupp, invFun := fun p => ⟨p⟩, left_inv := fun ⟨p⟩ => rfl, right_inv := fun p => rfl,
    map_mul' := by
      rintro ⟨⟩ ⟨⟩
      simp [mul_to_finsupp],
    map_add' := by
      rintro ⟨⟩ ⟨⟩
      simp [add_to_finsupp] }

/--  Ring isomorphism between `(polynomial R)ᵐᵒᵖ` and `polynomial Rᵐᵒᵖ`. -/
@[simps]
def op_ring_equiv : Polynomial Rᵐᵒᵖ ≃+* Polynomial (Rᵐᵒᵖ) :=
  ((to_finsupp_iso R).op.trans AddMonoidAlgebra.opRingEquiv).trans (to_finsupp_iso _).symm

variable {R}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_to_finsupp [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" (Term.app `AddMonoidAlgebra [`R (termℕ "ℕ")]))] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.paren
       "("
       [(Term.anonymousCtor "⟨" [(Term.app `f [`i])] "⟩") [(Term.typeAscription ":" (Term.app `Polynomial [`R]))]]
       ")"))
     "="
     (Term.anonymousCtor
      "⟨"
      [(Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        " in "
        `s
        ", "
        (Term.app `f [`i]))]
      "⟩"))))
  (Command.declValSimple
   ":="
   (Term.proj
    (Term.app
     (Term.proj (Term.proj (Term.proj (Term.app `to_finsupp_iso [`R]) "." `symm) "." `toAddMonoidHom) "." `map_sum)
     [`f `s])
    "."
    `symm)
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.proj (Term.proj (Term.proj (Term.app `to_finsupp_iso [`R]) "." `symm) "." `toAddMonoidHom) "." `map_sum)
    [`f `s])
   "."
   `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj (Term.proj (Term.proj (Term.app `to_finsupp_iso [`R]) "." `symm) "." `toAddMonoidHom) "." `map_sum)
   [`f `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.proj (Term.app `to_finsupp_iso [`R]) "." `symm) "." `toAddMonoidHom) "." `map_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj (Term.app `to_finsupp_iso [`R]) "." `symm) "." `toAddMonoidHom)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `to_finsupp_iso [`R]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `to_finsupp_iso [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `to_finsupp_iso
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `to_finsupp_iso [`R]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.proj (Term.proj (Term.paren "(" [(Term.app `to_finsupp_iso [`R]) []] ")") "." `symm) "." `toAddMonoidHom)
    "."
    `map_sum)
   [`f `s])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.paren
     "("
     [(Term.anonymousCtor "⟨" [(Term.app `f [`i])] "⟩") [(Term.typeAscription ":" (Term.app `Polynomial [`R]))]]
     ")"))
   "="
   (Term.anonymousCtor
    "⟨"
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `f [`i]))]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     " in "
     `s
     ", "
     (Term.app `f [`i]))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sum_to_finsupp
  { ι : Type _ } ( s : Finset ι ) ( f : ι → AddMonoidAlgebra R ℕ )
    : ∑ i in s , ( ⟨ f i ⟩ : Polynomial R ) = ⟨ ∑ i in s , f i ⟩
  := to_finsupp_iso R . symm . toAddMonoidHom . map_sum f s . symm

/-- 
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support : Polynomial R → Finset ℕ
  | ⟨p⟩ => p.support

@[simp]
theorem support_zero : (0 : Polynomial R).Support = ∅ :=
  rfl

@[simp]
theorem support_eq_empty : p.support = ∅ ↔ p = 0 := by
  rcases p with ⟨⟩
  simp [support, ← zero_to_finsupp]

theorem card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by
  simp

/--  `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] Polynomial R :=
  { toFun := monomial_fun n,
    map_add' := by
      simp [monomial_fun, add_to_finsupp],
    map_smul' := by
      simp [monomial_fun, smul_to_finsupp] }

@[simp]
theorem monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 :=
  (monomial n).map_zero

theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  rfl

theorem monomial_add (n : ℕ) (r s : R) : monomial n (r+s) = monomial n r+monomial n s :=
  (monomial n).map_add _ _

theorem monomial_mul_monomial (n m : ℕ) (r s : R) : (monomial n r*monomial m s) = monomial (n+m) (r*s) := by
  simp only [monomial, monomial_fun, LinearMap.coe_mk, mul_to_finsupp, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem monomial_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r ^ k = monomial (n*k) (r ^ k) := by
  induction' k with k ih
  ·
    simp [pow_zeroₓ, monomial_zero_one]
  ·
    simp [pow_succₓ, ih, monomial_mul_monomial, Nat.succ_eq_add_one, mul_addₓ, add_commₓ]

theorem smul_monomial {S} [Monoidₓ S] [DistribMulAction S R] (a : S) (n : ℕ) (b : R) :
    a • monomial n b = monomial n (a • b) := by
  simp [monomial, monomial_fun, smul_to_finsupp]

@[simp]
theorem to_finsupp_iso_monomial : (to_finsupp_iso R) (monomial n a) = single n a := by
  simp [to_finsupp_iso, monomial, monomial_fun]

@[simp]
theorem to_finsupp_iso_symm_single : (to_finsupp_iso R).symm (single n a) = monomial n a := by
  simp [to_finsupp_iso, monomial, monomial_fun]

theorem monomial_injective (n : ℕ) : Function.Injective (monomial n : R → Polynomial R) := by
  convert (to_finsupp_iso R).symm.Injective.comp (single_injective n)
  ext
  simp

@[simp]
theorem monomial_eq_zero_iff (t : R) (n : ℕ) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

theorem support_add : (p+q).Support ⊆ p.support ∪ q.support := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp only [add_to_finsupp, support]
  exact support_add

/-- 
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* Polynomial R :=
  { monomial 0 with
    map_one' := by
      simp [monomial_zero_one],
    map_mul' := by
      simp [monomial_mul_monomial],
    map_zero' := by
      simp }

@[simp]
theorem monomial_zero_left (a : R) : monomial 0 a = C a :=
  rfl

theorem C_0 : C (0 : R) = 0 := by
  simp

theorem C_1 : C (1 : R) = 1 :=
  rfl

theorem C_mul : C (a*b) = C a*C b :=
  C.map_mul a b

theorem C_add : C (a+b) = C a+C b :=
  C.map_add a b

@[simp]
theorem smul_C {S} [Monoidₓ S] [DistribMulAction S R] (s : S) (r : R) : s • C r = C (s • r) :=
  smul_monomial _ _ r

@[simp]
theorem C_bit0 : C (bit0 a) = bit0 (C a) :=
  C_add

@[simp]
theorem C_bit1 : C (bit1 a) = bit1 (C a) := by
  simp [bit1, C_bit0]

theorem C_pow : C (a ^ n) = C a ^ n :=
  C.map_pow a n

@[simp]
theorem C_eq_nat_cast (n : ℕ) : C (n : R) = (n : Polynomial R) :=
  C.map_nat_cast n

@[simp]
theorem C_mul_monomial : (C a*monomial n b) = monomial n (a*b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_addₓ]

@[simp]
theorem monomial_mul_C : (monomial n a*C b) = monomial n (a*b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zeroₓ]

/--  `X` is the polynomial variable (aka indeterminate). -/
def X : Polynomial R :=
  monomial 1 1

theorem monomial_one_one_eq_X : monomial 1 (1 : R) = X :=
  rfl

theorem monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction' n with n ih
  ·
    simp [monomial_zero_one]
  ·
    rw [pow_succₓ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, add_commₓ, one_mulₓ]

/--  `X` commutes with everything, even when the coefficients are noncommutative. -/
theorem X_mul : (X*p) = p*X := by
  rcases p with ⟨⟩
  simp only [X, monomial, monomial_fun, mul_to_finsupp, LinearMap.coe_mk]
  ext
  simp [AddMonoidAlgebra.mul_apply, sum_single_index, add_commₓ]

theorem X_pow_mul {n : ℕ} : ((X ^ n)*p) = p*X ^ n := by
  induction' n with n ih
  ·
    simp
  ·
    conv_lhs => rw [pow_succ'ₓ]
    rw [mul_assocₓ, X_mul, ← mul_assocₓ, ih, mul_assocₓ, ← pow_succ'ₓ]

theorem X_pow_mul_assoc {n : ℕ} : ((p*X ^ n)*q) = (p*q)*X ^ n := by
  rw [mul_assocₓ, X_pow_mul, ← mul_assocₓ]

theorem commute_X (p : Polynomial R) : Commute X p :=
  X_mul

theorem commute_X_pow (p : Polynomial R) (n : ℕ) : Commute (X ^ n) p :=
  X_pow_mul

@[simp]
theorem monomial_mul_X (n : ℕ) (r : R) : (monomial n r*X) = monomial (n+1) r := by
  erw [monomial_mul_monomial, mul_oneₓ]

@[simp]
theorem monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : (monomial n r*X ^ k) = monomial (n+k) r := by
  induction' k with k ih
  ·
    simp
  ·
    simp [ih, pow_succ'ₓ, ← mul_assocₓ, add_assocₓ]

@[simp]
theorem X_mul_monomial (n : ℕ) (r : R) : (X*monomial n r) = monomial (n+1) r := by
  rw [X_mul, monomial_mul_X]

@[simp]
theorem X_pow_mul_monomial (k n : ℕ) (r : R) : ((X ^ k)*monomial n r) = monomial (n+k) r := by
  rw [X_pow_mul, monomial_mul_X_pow]

/--  `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
def coeff : Polynomial R → ℕ → R
  | ⟨p⟩, n => p n

theorem coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 := by
  simp only [monomial, monomial_fun, coeff, LinearMap.coe_mk]
  rw [Finsupp.single_apply]

@[simp]
theorem coeff_zero (n : ℕ) : coeff (0 : Polynomial R) n = 0 :=
  rfl

@[simp]
theorem coeff_one_zero : coeff (1 : Polynomial R) 0 = 1 := by
  rw [← monomial_zero_one, coeff_monomial]
  simp

@[simp]
theorem coeff_X_one : coeff (X : Polynomial R) 1 = 1 :=
  coeff_monomial

@[simp]
theorem coeff_X_zero : coeff (X : Polynomial R) 0 = 0 :=
  coeff_monomial

@[simp]
theorem coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 := by
  simp [coeff_monomial]

theorem coeff_X : coeff (X : Polynomial R) n = if 1 = n then 1 else 0 :=
  coeff_monomial

theorem coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : Polynomial R) n = 0 := by
  rw [coeff_X, if_neg hn.symm]

@[simp]
theorem mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  rcases p with ⟨⟩
  simp [support, coeff]

theorem not_mem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by
  simp

theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert coeff_monomial using 2
  simp [eq_comm]

@[simp]
theorem coeff_C_zero : coeff (C a) 0 = a :=
  coeff_monomial

theorem coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by
  rw [coeff_C, if_neg h]

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : Nontrivial R :=
  ⟨⟨0, 1, fun h01 : 0 = 1 =>
      h $ by
        rw [← mul_oneₓ p, ← mul_oneₓ q, ← C_1, ← h01, C_0, mul_zero, mul_zero]⟩⟩

theorem monomial_eq_C_mul_X : ∀ {n}, monomial n a = C a*X ^ n
  | 0 => (mul_oneₓ _).symm
  | n+1 =>
    calc monomial (n+1) a = monomial n a*X := by
      rw [X, monomial_mul_monomial, mul_oneₓ]
      _ = (C a*X ^ n)*X := by
      rw [monomial_eq_C_mul_X]
      _ = C a*X ^ n+1 := by
      simp only [pow_addₓ, mul_assocₓ, pow_oneₓ]
      

@[simp]
theorem C_inj : C a = C b ↔ a = b :=
  ⟨fun h => coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_argₓ C⟩

@[simp]
theorem C_eq_zero : C a = 0 ↔ a = 0 :=
  calc C a = 0 ↔ C a = C 0 := by
    rw [C_0]
    _ ↔ a = 0 := C_inj
    

theorem ext_iff {p q : Polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp [coeff, Finsupp.ext_iff]

@[ext]
theorem ext {p q : Polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
  ext_iff.2

theorem add_hom_ext {M : Type _} [AddMonoidₓ M] {f g : Polynomial R →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g := by
  set f' : AddMonoidAlgebra R ℕ →+ M := f.comp (to_finsupp_iso R).symm with hf'
  set g' : AddMonoidAlgebra R ℕ →+ M := g.comp (to_finsupp_iso R).symm with hg'
  have : ∀ n a, f' (single n a) = g' (single n a) := fun n => by
    simp [hf', hg', h n]
  have A : f' = g' := Finsupp.add_hom_ext this
  have B : f = f'.comp (to_finsupp_iso R) := by
    ·
      rw [hf', AddMonoidHom.comp_assoc]
      ext x
      simp only [RingEquiv.symm_apply_apply, AddMonoidHom.coe_comp, Function.comp_app, RingHom.coe_add_monoid_hom,
        RingEquiv.coe_to_ring_hom, coe_coe]
  have C : g = g'.comp (to_finsupp_iso R) := by
    ·
      rw [hg', AddMonoidHom.comp_assoc]
      ext x
      simp only [RingEquiv.symm_apply_apply, AddMonoidHom.coe_comp, Function.comp_app, RingHom.coe_add_monoid_hom,
        RingEquiv.coe_to_ring_hom, coe_coe]
  rw [B, C, A]

@[ext]
theorem add_hom_ext' {M : Type _} [AddMonoidₓ M] {f g : Polynomial R →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  add_hom_ext fun n => AddMonoidHom.congr_fun (h n)

@[ext]
theorem lhom_ext' {M : Type _} [AddCommMonoidₓ M] [Module R M] {f g : Polynomial R →ₗ[R] M}
    (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) : f = g :=
  LinearMap.to_add_monoid_hom_injective $ add_hom_ext $ fun n => LinearMap.congr_fun (h n)

theorem eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : Polynomial R) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

theorem support_monomial n (a : R) (H : a ≠ 0) : (monomial n a).Support = singleton n := by
  simp [monomial, monomial_fun, support, Finsupp.support_single_ne_zero H]

theorem support_monomial' n (a : R) : (monomial n a).Support ⊆ singleton n := by
  simp [monomial, monomial_fun, support, Finsupp.support_single_subset]

theorem X_pow_eq_monomial n : X ^ n = monomial n (1 : R) := by
  induction' n with n hn
  ·
    rw [pow_zeroₓ, monomial_zero_one]
  ·
    rw [pow_succ'ₓ, hn, X, monomial_mul_monomial, one_mulₓ]

theorem monomial_eq_smul_X {n} : monomial n (a : R) = a • X ^ n :=
  calc monomial n a = monomial n (a*1) := by
    simp
    _ = a • monomial n 1 := by
    simp [monomial, monomial_fun, smul_to_finsupp]
    _ = a • X ^ n := by
    rw [X_pow_eq_monomial]
    

theorem support_X_pow (H : ¬(1 : R) = 0) (n : ℕ) : (X ^ n : Polynomial R).Support = singleton n := by
  convert support_monomial n 1 H
  exact X_pow_eq_monomial n

theorem support_X_empty (H : (1 : R) = 0) : (X : Polynomial R).Support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

theorem support_X (H : ¬(1 : R) = 0) : (X : Polynomial R).Support = singleton 1 := by
  rw [← pow_oneₓ X, support_X_pow H 1]

theorem monomial_left_inj {R : Type _} [Semiringₓ R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
    monomial i a = monomial j a ↔ i = j := by
  simp [monomial, monomial_fun, Finsupp.single_left_inj ha]

theorem nat_cast_mul {R : Type _} [Semiringₓ R] (n : ℕ) (p : Polynomial R) : ((n : Polynomial R)*p) = n • p :=
  (nsmul_eq_mul _ _).symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " Summing the values of a function applied to the coefficients of a polynomial -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Sum [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`S] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `AddCommMonoidₓ [`S]) "]")
    (Term.explicitBinder "(" [`p] [":" (Term.app `Polynomial [`R])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow `R "→" `S))] [] ")")]
   [(Term.typeSpec ":" `S)])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
    " in "
    `p.support
    ", "
    (Term.app `f [`n (Term.app `p.coeff [`n])]))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   " in "
   `p.support
   ", "
   (Term.app `f [`n (Term.app `p.coeff [`n])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`n (Term.app `p.coeff [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.coeff [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.coeff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.coeff [`n]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Summing the values of a function applied to the coefficients of a polynomial -/
  def
    Sum
    { S : Type _ } [ AddCommMonoidₓ S ] ( p : Polynomial R ) ( f : ℕ → R → S ) : S
    := ∑ n in p.support , f n p.coeff n

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_def [])
  (Command.declSig
   [(Term.implicitBinder "{" [`S] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `AddCommMonoidₓ [`S]) "]")
    (Term.explicitBinder "(" [`p] [":" (Term.app `Polynomial [`R])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow `R "→" `S))] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `p.sum [`f])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
      " in "
      `p.support
      ", "
      (Term.app `f [`n (Term.app `p.coeff [`n])])))))
  (Command.declValSimple ":=" `rfl [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `p.sum [`f])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
    " in "
    `p.support
    ", "
    (Term.app `f [`n (Term.app `p.coeff [`n])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   " in "
   `p.support
   ", "
   (Term.app `f [`n (Term.app `p.coeff [`n])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`n (Term.app `p.coeff [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.coeff [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.coeff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.coeff [`n]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sum_def
  { S : Type _ } [ AddCommMonoidₓ S ] ( p : Polynomial R ) ( f : ℕ → R → S )
    : p.sum f = ∑ n in p.support , f n p.coeff n
  := rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_eq_of_subset [])
  (Command.declSig
   [(Term.implicitBinder "{" [`S] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `AddCommMonoidₓ [`S]) "]")
    (Term.explicitBinder "(" [`p] [":" (Term.app `Polynomial [`R])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow `R "→" `S))] [] ")")
    (Term.explicitBinder
     "("
     [`hf]
     [":"
      (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_=_» (Term.app `f [`i (numLit "0")]) "=" (numLit "0")))]
     []
     ")")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [(termℕ "ℕ")])] [] ")")
    (Term.explicitBinder "(" [`hs] [":" (Init.Core.«term_⊆_» `p.support " ⊆ " `s)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `p.sum [`f])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
      " in "
      `s
      ", "
      (Term.app `f [`n (Term.app `p.coeff [`n])])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.apply
         "apply"
         (Term.app
          `Finset.sum_subset
          [`hs (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn `h'n] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_mem_support_iff)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h'n] []))])
        [])
       (group
        (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h'n) "," (Tactic.simpLemma [] [] `hf)] "]"] [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.apply
        "apply"
        (Term.app
         `Finset.sum_subset
         [`hs (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn `h'n] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_mem_support_iff)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`h'n] []))])
       [])
      (group
       (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h'n) "," (Tactic.simpLemma [] [] `hf)] "]"] [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h'n) "," (Tactic.simpLemma [] [] `hf)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h'n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `not_mem_support_iff)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`h'n] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h'n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `not_mem_support_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app
    `Finset.sum_subset
    [`hs (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn `h'n] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.sum_subset
   [`hs (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn `h'n] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hn `h'n] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `p.sum [`f])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
    " in "
    `s
    ", "
    (Term.app `f [`n (Term.app `p.coeff [`n])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   " in "
   `s
   ", "
   (Term.app `f [`n (Term.app `p.coeff [`n])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`n (Term.app `p.coeff [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.coeff [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.coeff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.coeff [`n]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sum_eq_of_subset
  { S : Type _ }
      [ AddCommMonoidₓ S ]
      ( p : Polynomial R )
      ( f : ℕ → R → S )
      ( hf : ∀ i , f i 0 = 0 )
      ( s : Finset ℕ )
      ( hs : p.support ⊆ s )
    : p.sum f = ∑ n in s , f n p.coeff n
  := by apply Finset.sum_subset hs fun n hn h'n => _ rw [ not_mem_support_iff ] at h'n simp [ h'n , hf ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " Expressing the product of two polynomials as a double sum. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `mul_eq_sum_sum [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Finset.Data.Finset.Fold.«term_*_» `p "*" `q)
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `p.support
      ", "
      (Term.app
       `q.sum
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`j `a] [])]
          "=>"
          (Term.app
           (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
           [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)])))])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.rcases "rcases" [(Tactic.casesTarget [] `p)] ["with" (Tactic.rcasesPat.tuple "⟨" [] "⟩")]) [])
       (group (Tactic.rcases "rcases" [(Tactic.casesTarget [] `q)] ["with" (Tactic.rcasesPat.tuple "⟨" [] "⟩")]) [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `mul_to_finsupp)
           ","
           (Tactic.simpLemma [] [] `support)
           ","
           (Tactic.simpLemma [] [] `monomial)
           ","
           (Tactic.simpLemma [] [] `Sum)
           ","
           (Tactic.simpLemma [] [] `monomial_fun)
           ","
           (Tactic.simpLemma [] [] `coeff)
           ","
           (Tactic.simpLemma [] [] `sum_to_finsupp)]
          "]"]
         [])
        [])
       (group (Tactic.tacticRfl "rfl") [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rcases "rcases" [(Tactic.casesTarget [] `p)] ["with" (Tactic.rcasesPat.tuple "⟨" [] "⟩")]) [])
      (group (Tactic.rcases "rcases" [(Tactic.casesTarget [] `q)] ["with" (Tactic.rcasesPat.tuple "⟨" [] "⟩")]) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `mul_to_finsupp)
          ","
          (Tactic.simpLemma [] [] `support)
          ","
          (Tactic.simpLemma [] [] `monomial)
          ","
          (Tactic.simpLemma [] [] `Sum)
          ","
          (Tactic.simpLemma [] [] `monomial_fun)
          ","
          (Tactic.simpLemma [] [] `coeff)
          ","
          (Tactic.simpLemma [] [] `sum_to_finsupp)]
         "]"]
        [])
       [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticRfl', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `mul_to_finsupp)
     ","
     (Tactic.simpLemma [] [] `support)
     ","
     (Tactic.simpLemma [] [] `monomial)
     ","
     (Tactic.simpLemma [] [] `Sum)
     ","
     (Tactic.simpLemma [] [] `monomial_fun)
     ","
     (Tactic.simpLemma [] [] `coeff)
     ","
     (Tactic.simpLemma [] [] `sum_to_finsupp)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_to_finsupp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coeff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `monomial_fun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `monomial
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_to_finsupp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases "rcases" [(Tactic.casesTarget [] `q)] ["with" (Tactic.rcasesPat.tuple "⟨" [] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `q
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases "rcases" [(Tactic.casesTarget [] `p)] ["with" (Tactic.rcasesPat.tuple "⟨" [] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Finset.Data.Finset.Fold.«term_*_» `p "*" `q)
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `p.support
    ", "
    (Term.app
     `q.sum
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j `a] [])]
        "=>"
        (Term.app
         (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
         [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `p.support
   ", "
   (Term.app
    `q.sum
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`j `a] [])]
       "=>"
       (Term.app
        (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
        [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `q.sum
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`j `a] [])]
      "=>"
      (Term.app
       (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
       [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j `a] [])]
    "=>"
    (Term.app
     (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
     [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
   [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `p.coeff [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.coeff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (Term.app `p.coeff [`i]) "*" `a) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `monomial [(Init.Logic.«term_+_» `i "+" `j)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `i "+" `j)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `i "+" `j) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `monomial
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `monomial [(Term.paren "(" [(Init.Logic.«term_+_» `i "+" `j) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `q.sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p.support
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Expressing the product of two polynomials as a double sum. -/
  theorem
    mul_eq_sum_sum
    : p * q = ∑ i in p.support , q.sum fun j a => monomial i + j p.coeff i * a
    :=
      by
        rcases p with ⟨ ⟩
          rcases q with ⟨ ⟩
          simp [ mul_to_finsupp , support , monomial , Sum , monomial_fun , coeff , sum_to_finsupp ]
          rfl

@[simp]
theorem sum_zero_index {S : Type _} [AddCommMonoidₓ S] (f : ℕ → R → S) : (0 : Polynomial R).Sum f = 0 := by
  simp [Sum]

@[simp]
theorem sum_monomial_index {S : Type _} [AddCommMonoidₓ S] (n : ℕ) (a : R) (f : ℕ → R → S) (hf : f n 0 = 0) :
    (monomial n a : Polynomial R).Sum f = f n a := by
  by_cases' h : a = 0
  ·
    simp [h, hf]
  ·
    simp [Sum, support_monomial, h, coeff_monomial]

@[simp]
theorem sum_C_index {a} {β} [AddCommMonoidₓ β] {f : ℕ → R → β} (h : f 0 0 = 0) : (C a).Sum f = f 0 a :=
  sum_monomial_index 0 a f h

@[simp]
theorem sum_X_index {S : Type _} [AddCommMonoidₓ S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
    (X : Polynomial R).Sum f = f 1 1 :=
  sum_monomial_index 1 1 f hf

theorem sum_add_index {S : Type _} [AddCommMonoidₓ S] (p q : Polynomial R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0)
    (h_add : ∀ a b₁ b₂, f a (b₁+b₂) = f a b₁+f a b₂) : (p+q).Sum f = p.sum f+q.sum f := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp only [add_to_finsupp, Sum, support, coeff, Pi.add_apply, coe_add]
  exact Finsupp.sum_add_index hf h_add

theorem sum_add' {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f g : ℕ → R → S) : p.sum (f+g) = p.sum f+p.sum g :=
  by
  simp [sum_def, Finset.sum_add_distrib]

theorem sum_add {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f g : ℕ → R → S) :
    (p.sum fun n x => f n x+g n x) = p.sum f+p.sum g :=
  sum_add' _ _ _

theorem sum_smul_index {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (b : R) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).Sum f = p.sum fun n a => f n (b*a) := by
  rcases p with ⟨⟩
  simp [smul_to_finsupp, Sum, support, coeff]
  exact Finsupp.sum_smul_index hf

/--  `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
irreducible_def erase (n : ℕ) : Polynomial R → Polynomial R
  | ⟨p⟩ => ⟨p.erase n⟩

@[simp]
theorem support_erase (p : Polynomial R) (n : ℕ) : support (p.erase n) = (support p).erase n := by
  rcases p with ⟨⟩
  simp only [support, erase, support_erase]

theorem monomial_add_erase (p : Polynomial R) (n : ℕ) : (monomial n (coeff p n)+p.erase n) = p := by
  rcases p with ⟨⟩
  simp [add_to_finsupp, monomial, monomial_fun, coeff, erase]
  exact Finsupp.single_add_erase _ _

theorem coeff_erase (p : Polynomial R) (n i : ℕ) : (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  rcases p with ⟨⟩
  simp only [erase, coeff]
  convert rfl

@[simp]
theorem erase_zero (n : ℕ) : (0 : Polynomial R).erase n = 0 := by
  simp [← zero_to_finsupp, erase]

@[simp]
theorem erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 := by
  simp [monomial, monomial_fun, erase, ← zero_to_finsupp]

@[simp]
theorem erase_same (p : Polynomial R) (n : ℕ) : coeff (p.erase n) n = 0 := by
  simp [coeff_erase]

@[simp]
theorem erase_ne (p : Polynomial R) (n i : ℕ) (h : i ≠ n) : coeff (p.erase n) i = coeff p i := by
  simp [coeff_erase, h]

section Update

/--  Replace the coefficient of a `p : polynomial p` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.nat_degree < n` and `a ≠ 0`, this increases the degree to `n`.  -/
def update (p : Polynomial R) (n : ℕ) (a : R) : Polynomial R :=
  Polynomial.of_finsupp (p.to_finsupp.update n a)

theorem coeff_update (p : Polynomial R) (n : ℕ) (a : R) : (p.update n a).coeff = Function.update p.coeff n a := by
  ext
  cases p
  simp only [coeff, update, Function.update_apply, coe_update]

theorem coeff_update_apply (p : Polynomial R) (n : ℕ) (a : R) (i : ℕ) :
    (p.update n a).coeff i = if i = n then a else p.coeff i := by
  rw [coeff_update, Function.update_apply]

@[simp]
theorem coeff_update_same (p : Polynomial R) (n : ℕ) (a : R) : (p.update n a).coeff n = a := by
  rw [p.coeff_update_apply, if_pos rfl]

theorem coeff_update_ne (p : Polynomial R) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) : (p.update n a).coeff i = p.coeff i :=
  by
  rw [p.coeff_update_apply, if_neg h]

@[simp]
theorem update_zero_eq_erase (p : Polynomial R) (n : ℕ) : p.update n 0 = p.erase n := by
  ext
  rw [coeff_update_apply, coeff_erase]

theorem support_update (p : Polynomial R) (n : ℕ) (a : R) [Decidable (a = 0)] :
    support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  cases p
  simp only [support, update, support_update]
  congr

theorem support_update_zero (p : Polynomial R) (n : ℕ) : support (p.update n 0) = p.support.erase n := by
  rw [update_zero_eq_erase, support_erase]

theorem support_update_ne_zero (p : Polynomial R) (n : ℕ) {a : R} (ha : a ≠ 0) :
    support (p.update n a) = insert n p.support := by
  classical <;> rw [support_update, if_neg ha]

end Update

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

instance : CommSemiringₓ (Polynomial R) :=
  { Polynomial.semiring with
    mul_comm := by
      rintro ⟨⟩ ⟨⟩
      simp [mul_to_finsupp, mul_commₓ] }

end CommSemiringₓ

section Ringₓ

variable [Ringₓ R]

instance : Ringₓ (Polynomial R) :=
  { Polynomial.semiring with neg := Neg.neg,
    add_left_neg := by
      rintro ⟨⟩
      simp [neg_to_finsupp, add_to_finsupp, ← zero_to_finsupp],
    zsmul := · • ·,
    zsmul_zero' := by
      rintro ⟨⟩
      simp [smul_to_finsupp, ← zero_to_finsupp],
    zsmul_succ' := by
      rintro n ⟨⟩
      simp [smul_to_finsupp, add_to_finsupp, add_smul, add_commₓ],
    zsmul_neg' := by
      rintro n ⟨⟩
      simp only [smul_to_finsupp, neg_to_finsupp]
      simp [add_smul, add_mulₓ] }

@[simp]
theorem coeff_neg (p : Polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := by
  rcases p with ⟨⟩
  simp [coeff, neg_to_finsupp]

@[simp]
theorem coeff_sub (p q : Polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := by
  rcases p with ⟨⟩
  rcases q with ⟨⟩
  simp [coeff, sub_eq_add_neg, add_to_finsupp, neg_to_finsupp]

@[simp]
theorem monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -monomial n a := by
  rw [eq_neg_iff_add_eq_zero, ← monomial_add, neg_add_selfₓ, monomial_zero_right]

@[simp]
theorem support_neg {p : Polynomial R} : (-p).Support = p.support := by
  rcases p with ⟨⟩
  simp [support, neg_to_finsupp]

end Ringₓ

instance [CommRingₓ R] : CommRingₓ (Polynomial R) :=
  { Polynomial.commSemiring, Polynomial.ring with }

section NonzeroSemiring

variable [Semiringₓ R] [Nontrivial R]

instance : Nontrivial (Polynomial R) := by
  have h : Nontrivial (AddMonoidAlgebra R ℕ) := by
    infer_instance
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩
  refine' ⟨⟨⟨x⟩, ⟨y⟩, _⟩⟩
  simp [hxy]

theorem X_ne_zero : (X : Polynomial R) ≠ 0 :=
  mt (congr_argₓ fun p => coeff p 1)
    (by
      simp )

end NonzeroSemiring

section reprₓ

variable [Semiringₓ R]

open_locale Classical

instance [HasRepr R] : HasRepr (Polynomial R) :=
  ⟨fun p =>
    if p = 0 then "0"
    else
      (p.support.sort (· ≤ ·)).foldr
        (fun n a =>
          (a ++ if a = "" then "" else " + ") ++
            if n = 0 then "C (" ++ reprₓ (coeff p n) ++ ")"
            else
              if n = 1 then if coeff p n = 1 then "X" else "C (" ++ reprₓ (coeff p n) ++ ") * X"
              else if coeff p n = 1 then "X ^ " ++ reprₓ n else "C (" ++ reprₓ (coeff p n) ++ ") * X ^ " ++ reprₓ n)
        ""⟩

end reprₓ

end Polynomial

