/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Data.Seq.Seq
import Algebra.Field.Defs

#align_import algebra.continued_fractions.basic from "leanprover-community/mathlib"@"fe8d0ff42c3c24d789f491dc2622b6cac3d61564"

/-!
# Basic Definitions/Theorems for Continued Fractions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convergents`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in
`convergents'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
fractions. We hence just call them `continued_fractions` in the library.
2. We use sequences from `data.seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/


-- Fix a carrier `α`.
variable (α : Type _)

/-!### Definitions-/


#print GenContFract.Pair /-
/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ,bᵢ⟩`. -/
protected structure GenContFract.Pair where
  a : α
  b : α
  deriving Inhabited
#align generalized_continued_fraction.pair GenContFract.Pair
-/

open GenContFract

/- ././././Mathport/Syntax/Translate/Command.lean:230:11: unsupported: unusual advanced open style -/
/-! Interlude: define some expected coercions and instances. -/


namespace GenContFract.Pair

variable {α}

/-- Make a `gcf.pair` printable. -/
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p => "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

#print GenContFract.Pair.map /-
/-- Maps a function `f` on both components of a given pair. -/
def map {β : Type _} (f : α → β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩
#align generalized_continued_fraction.pair.map GenContFract.Pair.map
-/

section coe

-- Fix another type `β` which we will convert to.
variable {β : Type _} [Coe α β]

/-- Coerce a pair by elementwise coercion. -/
instance hasCoeToGeneralizedContinuedFractionPair : Coe (Pair α) (Pair β) :=
  ⟨map coe⟩
#align generalized_continued_fraction.pair.has_coe_to_generalized_continued_fraction_pair GenContFract.Pair.hasCoeToGeneralizedContinuedFractionPair

#print GenContFract.Pair.coe_toPair /-
@[simp, norm_cast]
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) :=
  rfl
#align generalized_continued_fraction.pair.coe_to_generalized_continued_fraction_pair GenContFract.Pair.coe_toPair
-/

end coe

end GenContFract.Pair

variable (α)

#print GenContFract /-
/-- A *generalised continued fraction* (gcf) is a potentially infinite expression of the form
$$
  h + \dfrac{a_0}
            {b_0 + \dfrac{a_1}
                         {b_1 + \dfrac{a_2}
                                      {b_2 + \dfrac{a_3}
                                                   {b_3 + \dots}}}}
$$
where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf.
We store the sequence of partial numerators and denominators in a sequence of
generalized_continued_fraction.pairs `s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
structure GenContFract where
  h : α
  s : Seq <| Pair α
#align generalized_continued_fraction GenContFract
-/

variable {α}

namespace GenContFract

#print GenContFract.ofInteger /-
/-- Constructs a generalized continued fraction without fractional part. -/
def ofInteger (a : α) : GenContFract α :=
  ⟨a, Seq.nil⟩
#align generalized_continued_fraction.of_integer GenContFract.ofInteger
-/

instance [Inhabited α] : Inhabited (GenContFract α) :=
  ⟨ofInteger default⟩

#print GenContFract.partNums /-
/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partNums (g : GenContFract α) : Seq α :=
  g.s.map Pair.a
#align generalized_continued_fraction.partial_numerators GenContFract.partNums
-/

#print GenContFract.partDens /-
/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partDens (g : GenContFract α) : Seq α :=
  g.s.map Pair.b
#align generalized_continued_fraction.partial_denominators GenContFract.partDens
-/

#print GenContFract.TerminatedAt /-
/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def TerminatedAt (g : GenContFract α) (n : ℕ) : Prop :=
  g.s.TerminatedAt n
#align generalized_continued_fraction.terminated_at GenContFract.TerminatedAt
-/

#print GenContFract.terminatedAtDecidable /-
/-- It is decidable whether a gcf terminated at a given position. -/
instance terminatedAtDecidable (g : GenContFract α) (n : ℕ) : Decidable (g.TerminatedAt n) := by
  unfold terminated_at; infer_instance
#align generalized_continued_fraction.terminated_at_decidable GenContFract.terminatedAtDecidable
-/

#print GenContFract.Terminates /-
/-- A gcf terminates if its sequence terminates. -/
def Terminates (g : GenContFract α) : Prop :=
  g.s.Terminates
#align generalized_continued_fraction.terminates GenContFract.Terminates
-/

section coe

/-! Interlude: define some expected coercions. -/


-- Fix another type `β` which we will convert to.
variable {β : Type _} [Coe α β]

/-- Coerce a gcf by elementwise coercion. -/
instance hasCoeToGeneralizedContinuedFraction : Coe (GenContFract α) (GenContFract β) :=
  ⟨fun g => ⟨(g.h : β), (g.s.map coe : Seq <| Pair β)⟩⟩
#align generalized_continued_fraction.has_coe_to_generalized_continued_fraction GenContFract.hasCoeToGeneralizedContinuedFraction

#print GenContFract.coe_toGenContFract /-
@[simp, norm_cast]
theorem coe_toGenContFract {g : GenContFract α} :
    (↑(g : GenContFract α) : GenContFract β) = ⟨(g.h : β), (g.s.map coe : Seq <| Pair β)⟩ :=
  rfl
#align generalized_continued_fraction.coe_to_generalized_continued_fraction GenContFract.coe_toGenContFract
-/

end coe

end GenContFract

#print GenContFract.IsSimpContFract /-
/-- A generalized continued fraction is a *simple continued fraction* if all partial numerators are
equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
-/
def GenContFract.IsSimpContFract (g : GenContFract α) [One α] : Prop :=
  ∀ (n : ℕ) (aₙ : α), g.partNums.get? n = some aₙ → aₙ = 1
#align generalized_continued_fraction.is_simple_continued_fraction GenContFract.IsSimpContFract
-/

variable (α)

#print SimpContFract /-
/-- A *simple continued fraction* (scf) is a generalized continued fraction (gcf) whose partial
numerators are equal to one.
$$
  h + \dfrac{1}
            {b_0 + \dfrac{1}
                         {b_1 + \dfrac{1}
                                      {b_2 + \dfrac{1}
                                                   {b_3 + \dots}}}}
$$
For convenience, one often writes `[h; b₀, b₁, b₂,...]`.
It is encoded as the subtype of gcfs that satisfy
`generalized_continued_fraction.is_simple_continued_fraction`.
 -/
def SimpContFract [One α] :=
  { g : GenContFract α // g.IsSimpContFract }
#align simple_continued_fraction SimpContFract
-/

variable {α}

-- Interlude: define some expected coercions.
namespace SimpContFract

variable [One α]

#print SimpContFract.ofInteger /-
/-- Constructs a simple continued fraction without fractional part. -/
def ofInteger (a : α) : SimpContFract α :=
  ⟨GenContFract.ofInteger a, fun n aₙ h => by cases h⟩
#align simple_continued_fraction.of_integer SimpContFract.ofInteger
-/

instance : Inhabited (SimpContFract α) :=
  ⟨ofInteger 1⟩

/-- Lift a scf to a gcf using the inclusion map. -/
instance hasCoeToGeneralizedContinuedFraction : Coe (SimpContFract α) (GenContFract α) := by
  unfold SimpContFract; infer_instance
#align simple_continued_fraction.has_coe_to_generalized_continued_fraction SimpContFract.hasCoeToGeneralizedContinuedFraction

theorem coe_to_genContFract {s : SimpContFract α} : (↑s : GenContFract α) = s.val :=
  rfl
#align simple_continued_fraction.coe_to_generalized_continued_fraction SimpContFract.coe_to_genContFract

end SimpContFract

#print SimpContFract.IsContFract /-
/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if all partial denominators
`bᵢ` are positive, i.e. `0 < bᵢ`.
-/
def SimpContFract.IsContFract [One α] [Zero α] [LT α] (s : SimpContFract α) : Prop :=
  ∀ (n : ℕ) (bₙ : α), (↑s : GenContFract α).partDens.get? n = some bₙ → 0 < bₙ
#align simple_continued_fraction.is_continued_fraction SimpContFract.IsContFract
-/

variable (α)

#print ContFract /-
/-- A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose partial
denominators are all positive. It is the subtype of scfs that satisfy
`simple_continued_fraction.is_continued_fraction`.
 -/
def ContFract [One α] [Zero α] [LT α] :=
  { s : SimpContFract α // s.IsContFract }
#align continued_fraction ContFract
-/

variable {α}

/-! Interlude: define some expected coercions. -/


namespace ContFract

variable [One α] [Zero α] [LT α]

#print ContFract.ofInteger /-
/-- Constructs a continued fraction without fractional part. -/
def ofInteger (a : α) : ContFract α :=
  ⟨SimpContFract.ofInteger a, fun n bₙ h => by cases h⟩
#align continued_fraction.of_integer ContFract.ofInteger
-/

instance : Inhabited (ContFract α) :=
  ⟨ofInteger 0⟩

/-- Lift a cf to a scf using the inclusion map. -/
instance hasCoeToSimpleContinuedFraction : Coe (ContFract α) (SimpContFract α) := by
  unfold ContFract; infer_instance
#align continued_fraction.has_coe_to_simple_continued_fraction ContFract.hasCoeToSimpleContinuedFraction

theorem coe_to_simpContFract {c : ContFract α} : (↑c : SimpContFract α) = c.val :=
  rfl
#align continued_fraction.coe_to_simple_continued_fraction ContFract.coe_to_simpContFract

/-- Lift a cf to a scf using the inclusion map. -/
instance hasCoeToGeneralizedContinuedFraction : Coe (ContFract α) (GenContFract α) :=
  ⟨fun c => ↑(↑c : SimpContFract α)⟩
#align continued_fraction.has_coe_to_generalized_continued_fraction ContFract.hasCoeToGeneralizedContinuedFraction

theorem coe_to_genContFract {c : ContFract α} : (↑c : GenContFract α) = c.val :=
  rfl
#align continued_fraction.coe_to_generalized_continued_fraction ContFract.coe_to_genContFract

end ContFract

namespace GenContFract

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`algebra.continued_fractions.convergents_equiv`.
-/


-- Fix a division ring for the computations.
variable {K : Type _} [DivisionRing K]

/-!
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, `Bₙ` are called the *nth continuants*, Aₙ the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/


#print GenContFract.nextNum /-
/-- Returns the next numerator `Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, where `predA` is `Aₙ₋₁`,
`ppredA` is `Aₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextNum (a b ppredA predA : K) : K :=
  b * predA + a * ppredA
#align generalized_continued_fraction.next_numerator GenContFract.nextNum
-/

#print GenContFract.nextDen /-
/-- Returns the next denominator `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂``, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB
#align generalized_continued_fraction.next_denominator GenContFract.nextDen
-/

#print GenContFract.nextConts /-
/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `next_numerator` and `next_denominator`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩`, `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩
#align generalized_continued_fraction.next_continuants GenContFract.nextConts
-/

#print GenContFract.contsAux /-
/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def contsAux (g : GenContFract K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => continuants_aux (n + 1)
    | some gp => nextConts gp.a gp.b (continuants_aux n) (continuants_aux <| n + 1)
#align generalized_continued_fraction.continuants_aux GenContFract.contsAux
-/

#print GenContFract.conts /-
/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def conts (g : GenContFract K) : Stream' (Pair K) :=
  g.contsAux.tail
#align generalized_continued_fraction.continuants GenContFract.conts
-/

#print GenContFract.nums /-
/-- Returns the numerators `Aₙ` of `g`. -/
def nums (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.a
#align generalized_continued_fraction.numerators GenContFract.nums
-/

#print GenContFract.dens /-
/-- Returns the denominators `Bₙ` of `g`. -/
def dens (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.b
#align generalized_continued_fraction.denominators GenContFract.dens
-/

#print GenContFract.convs /-
/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convs (g : GenContFract K) : Stream' K := fun n : ℕ => g.nums n / g.dens n
#align generalized_continued_fraction.convergents GenContFract.convs
-/

#print GenContFract.convs'Aux /-
/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convergents'_aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convergents'_aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convs'Aux : Seq (Pair K) → ℕ → K
  | s, 0 => 0
  | s, n + 1 =>
    match s.headI with
    | none => 0
    | some gp => gp.a / (gp.b + convergents'_aux s.tail n)
#align generalized_continued_fraction.convergents'_aux GenContFract.convs'Aux
-/

#print GenContFract.convs' /-
/-- Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convergents' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convergents' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convs' (g : GenContFract K) (n : ℕ) : K :=
  g.h + convs'Aux g.s n
#align generalized_continued_fraction.convergents' GenContFract.convs'
-/

end GenContFract

-- Now, some basic, general theorems
namespace GenContFract

#print GenContFract.ext_iff /-
/-- Two gcfs `g` and `g'` are equal if and only if their components are equal. -/
protected theorem ext_iff {g g' : GenContFract α} : g = g' ↔ g.h = g'.h ∧ g.s = g'.s := by cases g;
  cases g'; simp
#align generalized_continued_fraction.ext_iff GenContFract.ext_iff
-/

#print GenContFract.ext /-
@[ext]
protected theorem ext {g g' : GenContFract α} (hyp : g.h = g'.h ∧ g.s = g'.s) : g = g' :=
  GenContFract.ext_iff.right hyp
#align generalized_continued_fraction.ext GenContFract.ext
-/

end GenContFract

