/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module ring_theory.witt_vector.compare
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.Truncated
import Mathbin.RingTheory.WittVector.Identities
import Mathbin.NumberTheory.Padics.RingHoms

/-!

# Comparison isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`

We construct a ring isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `zmod (p^n)`.

## Main declarations

* `witt_vector.to_zmod_pow`: a family of compatible ring homs `𝕎 (zmod p) → zmod (p^k)`
* `witt_vector.equiv`: the isomorphism

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

include hp

namespace TruncatedWittVector

variable (p) (n : ℕ) (R : Type _) [CommRing R]

theorem eq_of_le_of_cast_pow_eq_zero [CharP R p] (i : ℕ) (hin : i ≤ n)
    (hpi : (p ^ i : TruncatedWittVector p n R) = 0) : i = n :=
  by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi
  clear hpi
  have : (↑p ^ i : TruncatedWittVector p n R) = WittVector.truncate n (↑p ^ i) := by
    rw [RingHom.map_pow, map_nat_cast]
  rw [this, ext_iff, not_forall]
  clear this
  use ⟨i, hin⟩
  rw [WittVector.coeff_truncate, coeff_zero, Fin.coe_mk, WittVector.coeff_p_pow]
  haveI : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.1.ne_one
  exact one_ne_zero
#align
  truncated_witt_vector.eq_of_le_of_cast_pow_eq_zero TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero

section Iso

variable (p n) {R}

theorem card_zmod : Fintype.card (TruncatedWittVector p n (Zmod p)) = p ^ n := by
  rw [card, Zmod.card]
#align truncated_witt_vector.card_zmod TruncatedWittVector.card_zmod

theorem char_p_zmod : CharP (TruncatedWittVector p n (Zmod p)) (p ^ n) :=
  char_p_of_prime_pow_injective _ _ _ (card_zmod _ _) (eq_of_le_of_cast_pow_eq_zero p n (Zmod p))
#align truncated_witt_vector.char_p_zmod TruncatedWittVector.char_p_zmod

attribute [local instance] char_p_zmod

/-- The unique isomorphism between `zmod p^n` and `truncated_witt_vector p n (zmod p)`.

This isomorphism exists, because `truncated_witt_vector p n (zmod p)` is a finite ring
with characteristic and cardinality `p^n`.
-/
def zmodEquivTrunc : Zmod (p ^ n) ≃+* TruncatedWittVector p n (Zmod p) :=
  Zmod.ringEquiv (TruncatedWittVector p n (Zmod p)) (card_zmod _ _)
#align truncated_witt_vector.zmod_equiv_trunc TruncatedWittVector.zmodEquivTrunc

theorem zmod_equiv_trunc_apply {x : Zmod (p ^ n)} :
    zmodEquivTrunc p n x = Zmod.castHom (by rfl) (TruncatedWittVector p n (Zmod p)) x :=
  rfl
#align truncated_witt_vector.zmod_equiv_trunc_apply TruncatedWittVector.zmod_equiv_trunc_apply

/-- The following diagram commutes:
```text
          zmod (p^n) ----------------------------> zmod (p^m)
            |                                        |
            |                                        |
            v                                        v
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
```
Here the vertical arrows are `truncated_witt_vector.zmod_equiv_trunc`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
theorem commutes {m : ℕ} (hm : n ≤ m) :
    (truncate hm).comp (zmodEquivTrunc p m).toRingHom =
      (zmodEquivTrunc p n).toRingHom.comp (Zmod.castHom (pow_dvd_pow p hm) _) :=
  RingHom.ext_zmod _ _
#align truncated_witt_vector.commutes TruncatedWittVector.commutes

theorem commutes' {m : ℕ} (hm : n ≤ m) (x : Zmod (p ^ m)) :
    truncate hm (zmodEquivTrunc p m x) = zmodEquivTrunc p n (Zmod.castHom (pow_dvd_pow p hm) _ x) :=
  show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm] <;> rfl
#align truncated_witt_vector.commutes' TruncatedWittVector.commutes'

theorem commutes_symm' {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m (Zmod p)) :
    (zmodEquivTrunc p n).symm (truncate hm x) =
      Zmod.castHom (pow_dvd_pow p hm) _ ((zmodEquivTrunc p m).symm x) :=
  by
  apply (zmod_equiv_trunc p n).Injective
  rw [← commutes']
  simp
#align truncated_witt_vector.commutes_symm' TruncatedWittVector.commutes_symm'

/-- The following diagram commutes:
```text
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
            |                                        |
            |                                        |
            v                                        v
          zmod (p^n) ----------------------------> zmod (p^m)
```
Here the vertical arrows are `(truncated_witt_vector.zmod_equiv_trunc p _).symm`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
theorem commutes_symm {m : ℕ} (hm : n ≤ m) :
    (zmodEquivTrunc p n).symm.toRingHom.comp (truncate hm) =
      (Zmod.castHom (pow_dvd_pow p hm) _).comp (zmodEquivTrunc p m).symm.toRingHom :=
  by ext <;> apply commutes_symm'
#align truncated_witt_vector.commutes_symm TruncatedWittVector.commutes_symm

end Iso

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (p)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`to_zmod_pow` is a family of compatible ring homs. We get this family by composing\n`truncated_witt_vector.zmod_equiv_trunc` (in right-to-left direction)\nwith `witt_vector.truncate`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toZmodPow [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Ring.«term_→+*_»
          (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
          " →+* "
          (Term.app `Zmod [(«term_^_» `p "^" `k)])))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `symm) "." `toRingHom)
         "."
         `comp)
        [(Term.app `truncate [`k])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `symm) "." `toRingHom)
        "."
        `comp)
       [(Term.app `truncate [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `truncate [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `truncate
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `truncate [`k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `symm) "." `toRingHom)
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `symm) "." `toRingHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zmodEquivTrunc [`p `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zmodEquivTrunc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zmodEquivTrunc [`p `k]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_»
       (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
       " →+* "
       (Term.app `Zmod [(«term_^_» `p "^" `k)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [(«term_^_» `p "^" `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `p "^" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `p "^" `k) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (RingTheory.WittVector.Compare.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RingTheory.WittVector.Compare.term𝕎', expected 'RingTheory.WittVector.Compare.term𝕎._@.RingTheory.WittVector.Compare._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `to_zmod_pow` is a family of compatible ring homs. We get this family by composing
    `truncated_witt_vector.zmod_equiv_trunc` (in right-to-left direction)
    with `witt_vector.truncate`.
    -/
  def
    toZmodPow
    ( k : ℕ ) : 𝕎 Zmod p →+* Zmod p ^ k
    := zmodEquivTrunc p k . symm . toRingHom . comp truncate k
#align witt_vector.to_zmod_pow WittVector.toZmodPow

theorem to_zmod_pow_compat (m n : ℕ) (h : m ≤ n) :
    (Zmod.castHom (pow_dvd_pow p h) (Zmod (p ^ m))).comp (toZmodPow p n) = toZmodPow p m :=
  calc
    (Zmod.castHom _ (Zmod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n)) =
        ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) :=
      by rw [commutes_symm, RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).symm.toRingHom.comp (truncate m) := by
      rw [RingHom.comp_assoc, truncate_comp_witt_vector_truncate]
    
#align witt_vector.to_zmod_pow_compat WittVector.to_zmod_pow_compat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`to_padic_int` lifts `to_zmod_pow : 𝕎 (zmod p) →+* zmod (p ^ k)` to a ring hom to `ℤ_[p]`\nusing `padic_int.lift`, the universal property of `ℤ_[p]`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toPadicInt [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Ring.«term_→+*_»
          (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
          " →+* "
          (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]")))])
      (Command.declValSimple
       ":="
       («term_<|_» `PadicInt.lift "<|" (Term.app `to_zmod_pow_compat [`p]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `PadicInt.lift "<|" (Term.app `to_zmod_pow_compat [`p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_zmod_pow_compat [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_zmod_pow_compat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `PadicInt.lift
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_»
       (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
       " →+* "
       (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (RingTheory.WittVector.Compare.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RingTheory.WittVector.Compare.term𝕎', expected 'RingTheory.WittVector.Compare.term𝕎._@.RingTheory.WittVector.Compare._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `to_padic_int` lifts `to_zmod_pow : 𝕎 (zmod p) →+* zmod (p ^ k)` to a ring hom to `ℤ_[p]`
    using `padic_int.lift`, the universal property of `ℤ_[p]`.
    -/
  def toPadicInt : 𝕎 Zmod p →+* ℤ_[ p ] := PadicInt.lift <| to_zmod_pow_compat p
#align witt_vector.to_padic_int WittVector.toPadicInt

theorem zmod_equiv_trunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (TruncatedWittVector.truncate hk).comp
        ((zmodEquivTrunc p k₂).toRingHom.comp (PadicInt.toZmodPow k₂)) =
      (zmodEquivTrunc p k₁).toRingHom.comp (PadicInt.toZmodPow k₁) :=
  by rw [← RingHom.comp_assoc, commutes, RingHom.comp_assoc, PadicInt.zmod_cast_comp_to_zmod_pow]
#align witt_vector.zmod_equiv_trunc_compat WittVector.zmod_equiv_trunc_compat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`from_padic_int` uses `witt_vector.lift` to lift `truncated_witt_vector.zmod_equiv_trunc`\ncomposed with `padic_int.to_zmod_pow` to a ring hom `ℤ_[p] →+* 𝕎 (zmod p)`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `fromPadicInt [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Ring.«term_→+*_»
          (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]")
          " →+* "
          (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])))])
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app
         `WittVector.lift
         [(Term.fun
           "fun"
           (Term.basicFun
            [`k]
            []
            "=>"
            (Term.app
             (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom) "." `comp)
             [(Term.app `PadicInt.toZmodPow [`k])])))])
        "<|"
        (Term.app `zmod_equiv_trunc_compat [(Term.hole "_")]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app
        `WittVector.lift
        [(Term.fun
          "fun"
          (Term.basicFun
           [`k]
           []
           "=>"
           (Term.app
            (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom) "." `comp)
            [(Term.app `PadicInt.toZmodPow [`k])])))])
       "<|"
       (Term.app `zmod_equiv_trunc_compat [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zmod_equiv_trunc_compat [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zmod_equiv_trunc_compat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app
       `WittVector.lift
       [(Term.fun
         "fun"
         (Term.basicFun
          [`k]
          []
          "=>"
          (Term.app
           (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom) "." `comp)
           [(Term.app `PadicInt.toZmodPow [`k])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`k]
        []
        "=>"
        (Term.app
         (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom) "." `comp)
         [(Term.app `PadicInt.toZmodPow [`k])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom) "." `comp)
       [(Term.app `PadicInt.toZmodPow [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PadicInt.toZmodPow [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PadicInt.toZmodPow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `PadicInt.toZmodPow [`k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `zmodEquivTrunc [`p `k]) "." `toRingHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zmodEquivTrunc [`p `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zmodEquivTrunc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zmodEquivTrunc [`p `k]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `WittVector.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `WittVector.lift
      [(Term.fun
        "fun"
        (Term.basicFun
         [`k]
         []
         "=>"
         (Term.app
          (Term.proj
           (Term.proj (Term.paren "(" (Term.app `zmodEquivTrunc [`p `k]) ")") "." `toRingHom)
           "."
           `comp)
          [(Term.paren "(" (Term.app `PadicInt.toZmodPow [`k]) ")")])))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_»
       (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]")
       " →+* "
       (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (RingTheory.WittVector.Compare.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RingTheory.WittVector.Compare.term𝕎', expected 'RingTheory.WittVector.Compare.term𝕎._@.RingTheory.WittVector.Compare._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `from_padic_int` uses `witt_vector.lift` to lift `truncated_witt_vector.zmod_equiv_trunc`
    composed with `padic_int.to_zmod_pow` to a ring hom `ℤ_[p] →+* 𝕎 (zmod p)`.
    -/
  def
    fromPadicInt
    : ℤ_[ p ] →+* 𝕎 Zmod p
    :=
      WittVector.lift fun k => zmodEquivTrunc p k . toRingHom . comp PadicInt.toZmodPow k
        <|
        zmod_equiv_trunc_compat _
#align witt_vector.from_padic_int WittVector.fromPadicInt

theorem to_padic_int_comp_from_padic_int :
    (toPadicInt p).comp (fromPadicInt p) = RingHom.id ℤ_[p] :=
  by
  rw [← PadicInt.to_zmod_pow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc, to_padic_int, PadicInt.lift_spec]
  simp only [from_padic_int, to_zmod_pow, RingHom.comp_id]
  rw [RingHom.comp_assoc, truncate_comp_lift, ← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
#align witt_vector.to_padic_int_comp_from_padic_int WittVector.to_padic_int_comp_from_padic_int

theorem to_padic_int_comp_from_padic_int_ext (x) :
    (toPadicInt p).comp (fromPadicInt p) x = RingHom.id ℤ_[p] x := by
  rw [to_padic_int_comp_from_padic_int]
#align
  witt_vector.to_padic_int_comp_from_padic_int_ext WittVector.to_padic_int_comp_from_padic_int_ext

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `from_padic_int_comp_to_padic_int [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app `fromPadicInt [`p]) "." `comp)
          [(Term.app `toPadicInt [`p])])
         "="
         (Term.app
          `RingHom.id
          [(Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `WittVector.hom_ext)
           []
           (Tactic.intro "intro" [`n])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `from_padic_int)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.comp_assoc)
              ","
              (Tactic.rwRule [] `truncate_comp_lift)
              ","
              (Tactic.rwRule [] `RingHom.comp_assoc)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `to_padic_int)
              ","
              (Tactic.simpLemma [] [] `to_zmod_pow)
              ","
              (Tactic.simpLemma [] [] `RingHom.comp_id)
              ","
              (Tactic.simpLemma [] [] `PadicInt.lift_spec)
              ","
              (Tactic.simpLemma [] [] `RingHom.id_comp)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.comp_assoc)
              ","
              (Tactic.simpLemma [] [] `RingEquiv.toRingHom_comp_symm_toRingHom)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `WittVector.hom_ext)
          []
          (Tactic.intro "intro" [`n])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `from_padic_int)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.comp_assoc)
             ","
             (Tactic.rwRule [] `truncate_comp_lift)
             ","
             (Tactic.rwRule [] `RingHom.comp_assoc)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `to_padic_int)
             ","
             (Tactic.simpLemma [] [] `to_zmod_pow)
             ","
             (Tactic.simpLemma [] [] `RingHom.comp_id)
             ","
             (Tactic.simpLemma [] [] `PadicInt.lift_spec)
             ","
             (Tactic.simpLemma [] [] `RingHom.id_comp)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.comp_assoc)
             ","
             (Tactic.simpLemma [] [] `RingEquiv.toRingHom_comp_symm_toRingHom)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `to_padic_int)
         ","
         (Tactic.simpLemma [] [] `to_zmod_pow)
         ","
         (Tactic.simpLemma [] [] `RingHom.comp_id)
         ","
         (Tactic.simpLemma [] [] `PadicInt.lift_spec)
         ","
         (Tactic.simpLemma [] [] `RingHom.id_comp)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `RingHom.comp_assoc)
         ","
         (Tactic.simpLemma [] [] `RingEquiv.toRingHom_comp_symm_toRingHom)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingEquiv.toRingHom_comp_symm_toRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.comp_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.id_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PadicInt.lift_spec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.comp_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_zmod_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_padic_int
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `from_padic_int)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `RingHom.comp_assoc)
         ","
         (Tactic.rwRule [] `truncate_comp_lift)
         ","
         (Tactic.rwRule [] `RingHom.comp_assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.comp_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `truncate_comp_lift
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.comp_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `from_padic_int
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`n])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `WittVector.hom_ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `WittVector.hom_ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj (Term.app `fromPadicInt [`p]) "." `comp) [(Term.app `toPadicInt [`p])])
       "="
       (Term.app
        `RingHom.id
        [(Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `RingHom.id
       [(Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (RingTheory.WittVector.Compare.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RingTheory.WittVector.Compare.term𝕎', expected 'RingTheory.WittVector.Compare.term𝕎._@.RingTheory.WittVector.Compare._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  from_padic_int_comp_to_padic_int
  : fromPadicInt p . comp toPadicInt p = RingHom.id 𝕎 Zmod p
  :=
    by
      apply WittVector.hom_ext
        intro n
        rw [ from_padic_int , ← RingHom.comp_assoc , truncate_comp_lift , RingHom.comp_assoc ]
        simp
          only
          [
            to_padic_int
              ,
              to_zmod_pow
              ,
              RingHom.comp_id
              ,
              PadicInt.lift_spec
              ,
              RingHom.id_comp
              ,
              ← RingHom.comp_assoc
              ,
              RingEquiv.toRingHom_comp_symm_toRingHom
            ]
#align witt_vector.from_padic_int_comp_to_padic_int WittVector.from_padic_int_comp_to_padic_int

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `from_padic_int_comp_to_padic_int_ext [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj (Term.app `fromPadicInt [`p]) "." `comp)
          [(Term.app `toPadicInt [`p]) `x])
         "="
         (Term.app
          `RingHom.id
          [(Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])]) `x]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `from_padic_int_comp_to_padic_int)] "]")
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `from_padic_int_comp_to_padic_int)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `from_padic_int_comp_to_padic_int)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `from_padic_int_comp_to_padic_int
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (Term.proj (Term.app `fromPadicInt [`p]) "." `comp)
        [(Term.app `toPadicInt [`p]) `x])
       "="
       (Term.app
        `RingHom.id
        [(Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])]) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `RingHom.id
       [(Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (RingTheory.WittVector.Compare.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RingTheory.WittVector.Compare.term𝕎', expected 'RingTheory.WittVector.Compare.term𝕎._@.RingTheory.WittVector.Compare._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  from_padic_int_comp_to_padic_int_ext
  ( x ) : fromPadicInt p . comp toPadicInt p x = RingHom.id 𝕎 Zmod p x
  := by rw [ from_padic_int_comp_to_padic_int ]
#align
  witt_vector.from_padic_int_comp_to_padic_int_ext WittVector.from_padic_int_comp_to_padic_int_ext

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic integers. This\nequivalence is witnessed by `witt_vector.to_padic_int` with inverse `witt_vector.from_padic_int`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `equiv [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Ring.Equiv.«term_≃+*_»
          (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
          " ≃+* "
          (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]")))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `toFun [] [] ":=" (Term.app `toPadicInt [`p]))))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `invFun [] [] ":=" (Term.app `fromPadicInt [`p]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `left_inv
           []
           []
           ":="
           (Term.app `from_padic_int_comp_to_padic_int_ext [(Term.hole "_")]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `right_inv
           []
           []
           ":="
           (Term.app `to_padic_int_comp_from_padic_int_ext [(Term.hole "_")]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl `map_mul' [] [] ":=" (Term.app `RingHom.map_mul [(Term.hole "_")]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl `map_add' [] [] ":=" (Term.app `RingHom.map_add [(Term.hole "_")]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RingHom.map_add [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.map_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `RingHom.map_mul [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `RingHom.map_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_padic_int_comp_from_padic_int_ext [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_padic_int_comp_from_padic_int_ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `from_padic_int_comp_to_padic_int_ext [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `from_padic_int_comp_to_padic_int_ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `fromPadicInt [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fromPadicInt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `toPadicInt [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `toPadicInt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Ring.Equiv.«term_≃+*_»
       (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
       " ≃+* "
       (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Padics.PadicIntegers.«termℤ_[_]» "ℤ_[" `p "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (RingTheory.WittVector.Compare.term𝕎 "𝕎") [(Term.app `Zmod [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Zmod [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (RingTheory.WittVector.Compare.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'RingTheory.WittVector.Compare.term𝕎', expected 'RingTheory.WittVector.Compare.term𝕎._@.RingTheory.WittVector.Compare._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic integers. This
    equivalence is witnessed by `witt_vector.to_padic_int` with inverse `witt_vector.from_padic_int`.
    -/
  def
    equiv
    : 𝕎 Zmod p ≃+* ℤ_[ p ]
    where
      toFun := toPadicInt p
        invFun := fromPadicInt p
        left_inv := from_padic_int_comp_to_padic_int_ext _
        right_inv := to_padic_int_comp_from_padic_int_ext _
        map_mul' := RingHom.map_mul _
        map_add' := RingHom.map_add _
#align witt_vector.equiv WittVector.equiv

end WittVector

