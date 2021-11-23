import Mathbin.Data.Seq.Seq 
import Mathbin.Algebra.Field.Basic

/-!
# Basic Definitions/Theorems for Continued Fractions

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


variable(α : Type _)

/-!### Definitions-/


-- error in Algebra.ContinuedFractions.Basic: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/-- We collect a partial numerator `aᵢ` and partial denominator `bᵢ` in a pair `⟨aᵢ,bᵢ⟩`. -/
@[derive #[expr inhabited]]
protected
structure generalized_continued_fraction.pair := (a : α) (b : α)

open GeneralizedContinuedFraction

/-! Interlude: define some expected coercions and instances. -/


namespace GeneralizedContinuedFraction.Pair

variable{α}

/-- Make a `gcf.pair` printable. -/
instance  [HasRepr α] : HasRepr (pair α) :=
  ⟨fun p => "(a : " ++ reprₓ p.a ++ ", b : " ++ reprₓ p.b ++ ")"⟩

/-- Maps a function `f` on both components of a given pair. -/
def map {β : Type _} (f : α → β) (gp : pair α) : pair β :=
  ⟨f gp.a, f gp.b⟩

section coeₓ

variable{β : Type _}[Coe α β]

/-- Coerce a pair by elementwise coercion. -/
instance has_coe_to_generalized_continued_fraction_pair : Coe (pair α) (pair β) :=
  ⟨map coeₓ⟩

@[simp, normCast]
theorem coe_to_generalized_continued_fraction_pair {a b : α} :
  («expr↑ » (pair.mk a b) : pair β) = pair.mk (a : β) (b : β) :=
  rfl

end coeₓ

end GeneralizedContinuedFraction.Pair

variable(α)

/--
A *generalised continued fraction* (gcf) is a potentially infinite expression of the form

                                a₀
                h + ---------------------------
                                  a₁
                      b₀ + --------------------
                                    a₂
                            b₁ + --------------
                                        a₃
                                  b₂ + --------
                                      b₃ + ...

where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf.
We store the sequence of partial numerators and denominators in a sequence of
generalized_continued_fraction.pairs `s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
structure GeneralizedContinuedFraction where 
  h : α 
  s : Seqₓₓ$ pair α

variable{α}

namespace GeneralizedContinuedFraction

/-- Constructs a generalized continued fraction without fractional part. -/
def of_integer (a : α) : GeneralizedContinuedFraction α :=
  ⟨a, Seqₓₓ.nil⟩

instance  [Inhabited α] : Inhabited (GeneralizedContinuedFraction α) :=
  ⟨of_integer (default _)⟩

/-- Returns the sequence of partial numerators `aᵢ` of `g`. -/
def partial_numerators (g : GeneralizedContinuedFraction α) : Seqₓₓ α :=
  g.s.map pair.a

/-- Returns the sequence of partial denominators `bᵢ` of `g`. -/
def partial_denominators (g : GeneralizedContinuedFraction α) : Seqₓₓ α :=
  g.s.map pair.b

/-- A gcf terminated at position `n` if its sequence terminates at position `n`. -/
def terminated_at (g : GeneralizedContinuedFraction α) (n : ℕ) : Prop :=
  g.s.terminated_at n

/-- It is decidable whether a gcf terminated at a given position. -/
instance terminated_at_decidable (g : GeneralizedContinuedFraction α) (n : ℕ) : Decidable (g.terminated_at n) :=
  by 
    unfold terminated_at 
    infer_instance

/-- A gcf terminates if its sequence terminates. -/
def terminates (g : GeneralizedContinuedFraction α) : Prop :=
  g.s.terminates

section coeₓ

/-! Interlude: define some expected coercions. -/


variable{β : Type _}[Coe α β]

/-- Coerce a gcf by elementwise coercion. -/
instance has_coe_to_generalized_continued_fraction :
  Coe (GeneralizedContinuedFraction α) (GeneralizedContinuedFraction β) :=
  ⟨fun g => ⟨(g.h : β), (g.s.map coeₓ : Seqₓₓ$ pair β)⟩⟩

@[simp, normCast]
theorem coe_to_generalized_continued_fraction {g : GeneralizedContinuedFraction α} :
  («expr↑ » (g : GeneralizedContinuedFraction α) : GeneralizedContinuedFraction β) =
    ⟨(g.h : β), (g.s.map coeₓ : Seqₓₓ$ pair β)⟩ :=
  rfl

end coeₓ

end GeneralizedContinuedFraction

/--
A generalized continued fraction is a *simple continued fraction* if all partial numerators are
equal to one.

                                1
                h + ---------------------------
                                  1
                      b₀ + --------------------
                                    1
                            b₁ + --------------
                                        1
                                  b₂ + --------
                                      b₃ + ...

-/
def GeneralizedContinuedFraction.IsSimpleContinuedFraction (g : GeneralizedContinuedFraction α) [HasOne α] : Prop :=
  ∀ n : ℕ aₙ : α, g.partial_numerators.nth n = some aₙ → aₙ = 1

variable(α)

/--
A *simple continued fraction* (scf) is a generalized continued fraction (gcf) whose partial
numerators are equal to one.

                                1
                h + ---------------------------
                                  1
                      b₀ + --------------------
                                    1
                            b₁ + --------------
                                        1
                                  b₂ + --------
                                      b₃ + ...

For convenience, one often writes `[h; b₀, b₁, b₂,...]`.
It is encoded as the subtype of gcfs that satisfy
`generalized_continued_fraction.is_simple_continued_fraction`.
 -/
def SimpleContinuedFraction [HasOne α] :=
  { g : GeneralizedContinuedFraction α // g.is_simple_continued_fraction }

variable{α}

namespace SimpleContinuedFraction

variable[HasOne α]

/-- Constructs a simple continued fraction without fractional part. -/
def of_integer (a : α) : SimpleContinuedFraction α :=
  ⟨GeneralizedContinuedFraction.ofInteger a,
    fun n aₙ h =>
      by 
        cases h⟩

instance  : Inhabited (SimpleContinuedFraction α) :=
  ⟨of_integer 1⟩

/-- Lift a scf to a gcf using the inclusion map. -/
instance has_coe_to_generalized_continued_fraction : Coe (SimpleContinuedFraction α) (GeneralizedContinuedFraction α) :=
  by 
    unfold SimpleContinuedFraction 
    infer_instance

theorem coe_to_generalized_continued_fraction {s : SimpleContinuedFraction α} :
  («expr↑ » s : GeneralizedContinuedFraction α) = s.val :=
  rfl

end SimpleContinuedFraction

/--
A simple continued fraction is a *(regular) continued fraction* ((r)cf) if all partial denominators
`bᵢ` are positive, i.e. `0 < bᵢ`.
-/
def SimpleContinuedFraction.IsContinuedFraction [HasOne α] [HasZero α] [LT α] (s : SimpleContinuedFraction α) : Prop :=
  ∀ n : ℕ bₙ : α, («expr↑ » s : GeneralizedContinuedFraction α).partialDenominators.nth n = some bₙ → 0 < bₙ

variable(α)

/--
A *(regular) continued fraction* ((r)cf) is a simple continued fraction (scf) whose partial
denominators are all positive. It is the subtype of scfs that satisfy
`simple_continued_fraction.is_continued_fraction`.
 -/
def ContinuedFraction [HasOne α] [HasZero α] [LT α] :=
  { s : SimpleContinuedFraction α // s.is_continued_fraction }

variable{α}

/-! Interlude: define some expected coercions. -/


namespace ContinuedFraction

variable[HasOne α][HasZero α][LT α]

/-- Constructs a continued fraction without fractional part. -/
def of_integer (a : α) : ContinuedFraction α :=
  ⟨SimpleContinuedFraction.ofInteger a,
    fun n bₙ h =>
      by 
        cases h⟩

instance  : Inhabited (ContinuedFraction α) :=
  ⟨of_integer 0⟩

/-- Lift a cf to a scf using the inclusion map. -/
instance has_coe_to_simple_continued_fraction : Coe (ContinuedFraction α) (SimpleContinuedFraction α) :=
  by 
    unfold ContinuedFraction 
    infer_instance

theorem coe_to_simple_continued_fraction {c : ContinuedFraction α} : («expr↑ » c : SimpleContinuedFraction α) = c.val :=
  rfl

/-- Lift a cf to a scf using the inclusion map. -/
instance has_coe_to_generalized_continued_fraction : Coe (ContinuedFraction α) (GeneralizedContinuedFraction α) :=
  ⟨fun c => «expr↑ » («expr↑ » c : SimpleContinuedFraction α)⟩

theorem coe_to_generalized_continued_fraction {c : ContinuedFraction α} :
  («expr↑ » c : GeneralizedContinuedFraction α) = c.val :=
  rfl

end ContinuedFraction

namespace GeneralizedContinuedFraction

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`algebra.continued_fractions.convergents_equiv`.
-/


variable{K : Type _}[DivisionRing K]

/-!
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, `Bₙ` are called the *nth continuants*, Aₙ the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/


/--
Returns the next numerator `Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, where `predA` is `Aₙ₋₁`,
`ppredA` is `Aₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def next_numerator (a b ppredA predA : K) : K :=
  (b*predA)+a*ppredA

/--
Returns the next denominator `Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂``, where `predB` is `Bₙ₋₁` and
`ppredB` is `Bₙ₋₂`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def next_denominator (aₙ bₙ ppredB predB : K) : K :=
  (bₙ*predB)+aₙ*ppredB

/--
Returns the next continuants `⟨Aₙ, Bₙ⟩` using `next_numerator` and `next_denominator`, where `pred`
is `⟨Aₙ₋₁, Bₙ₋₁⟩`, `ppred` is `⟨Aₙ₋₂, Bₙ₋₂⟩`, `a` is `aₙ₋₁`, and `b` is `bₙ₋₁`.
-/
def next_continuants (a b : K) (ppred pred : pair K) : pair K :=
  ⟨next_numerator a b ppred.a pred.a, next_denominator a b ppred.b pred.b⟩

/-- Returns the continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of `g`. -/
def continuants_aux (g : GeneralizedContinuedFraction K) : Streamₓ (pair K)
| 0 => ⟨1, 0⟩
| 1 => ⟨g.h, 1⟩
| n+2 =>
  match g.s.nth n with 
  | none => continuants_aux (n+1)
  | some gp => next_continuants gp.a gp.b (continuants_aux n) (continuants_aux$ n+1)

/-- Returns the continuants `⟨Aₙ, Bₙ⟩` of `g`. -/
def continuants (g : GeneralizedContinuedFraction K) : Streamₓ (pair K) :=
  g.continuants_aux.tail

/-- Returns the numerators `Aₙ` of `g`. -/
def numerators (g : GeneralizedContinuedFraction K) : Streamₓ K :=
  g.continuants.map pair.a

/-- Returns the denominators `Bₙ` of `g`. -/
def denominators (g : GeneralizedContinuedFraction K) : Streamₓ K :=
  g.continuants.map pair.b

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convergents (g : GeneralizedContinuedFraction K) : Streamₓ K :=
  fun n : ℕ => g.numerators n / g.denominators n

/--
Returns the approximation of the fraction described by the given sequence up to a given position n.
For example, `convergents'_aux [(1, 2), (3, 4), (5, 6)] 2 = 1 / (2 + 3 / 4)` and
`convergents'_aux [(1, 2), (3, 4), (5, 6)] 0 = 0`.
-/
def convergents'_aux : Seqₓₓ (pair K) → ℕ → K
| s, 0 => 0
| s, n+1 =>
  match s.head with 
  | none => 0
  | some gp => gp.a / gp.b+convergents'_aux s.tail n

/--
Returns the convergents of `g` by evaluating the fraction described by `g` up to a given
position `n`. For example, `convergents' [9; (1, 2), (3, 4), (5, 6)] 2 = 9 + 1 / (2 + 3 / 4)` and
`convergents' [9; (1, 2), (3, 4), (5, 6)] 0 = 9`
-/
def convergents' (g : GeneralizedContinuedFraction K) (n : ℕ) : K :=
  g.h+convergents'_aux g.s n

end GeneralizedContinuedFraction

namespace GeneralizedContinuedFraction

/-- Two gcfs `g` and `g'` are equal if and only if their components are equal. -/
protected theorem ext_iff {g g' : GeneralizedContinuedFraction α} : g = g' ↔ g.h = g'.h ∧ g.s = g'.s :=
  by 
    cases g 
    cases g' 
    simp 

@[ext]
protected theorem ext {g g' : GeneralizedContinuedFraction α} (hyp : g.h = g'.h ∧ g.s = g'.s) : g = g' :=
  GeneralizedContinuedFraction.ext_iff.elim_right hyp

end GeneralizedContinuedFraction

