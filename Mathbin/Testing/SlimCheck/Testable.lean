/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Testing.SlimCheck.Sampleable

/-!
# `testable` Class

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `testable` and `sampleable` are the means by which
`slim_check` creates samples and tests them. For instance, the proposition
`∀ i j : ℕ, i ≤ j` has a `testable` instance because `ℕ` is sampleable
and `i ≤ j` is decidable. Once `slim_check` finds the `testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. This allows the
user to create new instances and apply `slim_check` to new situations.

### Polymorphism

The property `testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys
= ys ++ xs)` shows us that type-polymorphic properties can be
tested. `α` is instantiated with `ℤ` first and then tested as normal
monomorphic properties.

The monomorphisation limits the applicability of `slim_check` to
polymorphic properties that can be stated about integers. The
limitation may be lifted in the future but, for now, if
one wishes to use a different type than `ℤ`, one has to refer to
the desired type.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:

```lean
structure my_type :=
(x y : ℕ)
(h : x ≤ y)
```

How do we test a property about `my_type`? For instance, let us consider
`testable.check $ ∀ a b : my_type, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `sampleable my_type`. We can define one as follows:

```lean
instance : sampleable my_type :=
{ sample := do
  x ← sample ℕ,
  xy_diff ← sample ℕ,
  return { x := x, y := x + xy_diff, h := /- some proof -/ } }
```

We can see that the instance is very simple because our type is built
up from other type that have `sampleable` instances. `sampleable` also
has a `shrink` method but it is optional. We may want to implement one
for ease of testing as:

```lean
/- ... -/
  shrink := λ ⟨x,y,h⟩, (λ ⟨x,y⟩, { x := x, y := x + y, h := /- proof -/}) <$> shrink (x, y - x) }
```

Again, we take advantage of the fact that other types have useful
`shrink` implementations, in this case `prod`.

### Optimizing the sampling

Some properties are guarded by a proposition. For instance, recall this
example:

```lean
#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100)
```

When testing the above example, we generate a natural number, we check
that it is even and test it if it is even or throw it away and start
over otherwise. Statistically, we can expect half of our samples to be
thrown away by such a filter. Sometimes, the filter is more
restrictive. For instance we might need `x` to be a `prime`
number. This would cause most of our samples to be discarded.

We can help `slim_check` find good samples by providing specialized
sampleable instances. Below, we show an instance for the subtype
of even natural numbers. This means that, when producing
a sample, it is forced to produce a proof that it is even.

```lean
instance {k : ℕ} [fact (0 < k)] : sampleable { x : ℕ // k ∣ x } :=
{ sample := do { n ← sample ℕ, pure ⟨k*n, dvd_mul_right _ _⟩ },
  shrink := λ ⟨x,h⟩, (λ y, ⟨k*y, dvd_mul_right _ _⟩) <$> shrink x }
```

Such instance will be preferred when testing a proposition of the shape
`∀ x : T, p x → q`

We can observe the effect by enabling tracing:

```lean
/- no specialized sampling -/
#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100) { trace_discarded := tt }
-- discard
--  x := 1
-- discard
--  x := 41
-- discard
--  x := 3
-- discard
--  x := 5
-- discard
--  x := 5
-- discard
--  x := 197
-- discard
--  x := 469
-- discard
--  x := 9
-- discard

-- ===================
-- Found problems!

-- x := 552
-- -------------------

/- let us define a specialized sampling instance -/
instance {k : ℕ} : sampleable { x : ℕ // k ∣ x } :=
{ sample := do { n ← sample ℕ, pure ⟨k*n, dvd_mul_right _ _⟩ },
  shrink := λ ⟨x,h⟩, (λ y, ⟨k*y, dvd_mul_right _ _⟩) <$> shrink x }

#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100) { enable_tracing := tt }
-- ===================
-- Found problems!

-- x := 358
-- -------------------
```

Similarly, it is common to write properties of the form: `∀ i j, i ≤ j → ...`
as the following example show:

```lean
#eval check (∀ i j k : ℕ, j < k → i - k < i - j)
```

Without subtype instances, the above property discards many samples
because `j < k` does not hold. Fortunately, we have appropriate
instance to choose `k` intelligently.

## Main definitions
  * `testable` class
  * `testable.check`: a way to test a proposition using random examples

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/


universe u v

variable (var var' : String)

variable (α : Type u)

variable (β : α → Prop)

variable (f : Type → Prop)

namespace SlimCheck

/- ./././Mathport/Syntax/Translate/Command.lean:355:30: infer kinds are unsupported in Lean 4: gave_up {} -/
#print SlimCheck.TestResult /-
/-- Result of trying to disprove `p`

The constructors are:
  *  `success : (psum unit p) → test_result`
     succeed when we find another example satisfying `p`
     In `success h`, `h` is an optional proof of the proposition.
     Without the proof, all we know is that we found one example
     where `p` holds. With a proof, the one test was sufficient to
     prove that `p` holds and we do not need to keep finding examples.
   * `gave_up {} : ℕ → test_result`
     give up when a well-formed example cannot be generated.
     `gave_up n` tells us that `n` invalid examples were tried.
     Above 100, we give up on the proposition and report that we
     did not find a way to properly test it.
   * `failure : ¬ p → (list string) → ℕ → test_result`
     a counter-example to `p`; the strings specify values for the relevant variables.
     `failure h vs n` also carries a proof that `p` does not hold. This way, we can
     guarantee that there will be no false positive. The last component, `n`,
     is the number of times that the counter-example was shrunk.
-/
inductive TestResult (p : Prop)
  | success : PSum Unit p → test_result
  | gave_up : ℕ → test_result
  | failure : ¬p → List String → ℕ → test_result
  deriving Inhabited
#align slim_check.test_result SlimCheck.TestResult
-/

#print SlimCheck.TestResult.toString /-
/-- format a `test_result` as a string. -/
protected def TestResult.toString {p} : TestResult p → String
  | test_result.success (PSum.inl ()) => "success (without proof)"
  | test_result.success (PSum.inr h) => "success (with proof)"
  | test_result.gave_up n => s! "gave up {n} times"
  | test_result.failure a vs _ => s! "failed {vs}"
#align slim_check.test_result.to_string SlimCheck.TestResult.toString
-/

/-- configuration for testing a property -/
structure SlimCheckCfg where
  numInst : ℕ := 100
  -- number of examples
  maxSize : ℕ := 100
  -- final size argument
  traceDiscarded : Bool := false
  -- enable the printing out of discarded samples
  traceSuccess : Bool := false
  -- enable the printing out of successful tests
  traceShrink : Bool := false
  -- enable the printing out of shrinking steps
  traceShrinkCandidates : Bool := false
  -- enable the printing out of shrinking candidates
  randomSeed : Option ℕ := none
  -- specify a seed to the random number generator to
  -- obtain a deterministic behavior
  quiet : Bool := false
  deriving has_reflect, Inhabited
#align slim_check.slim_check_cfg SlimCheck.SlimCheckCfg

-- suppress success message when running `slim_check`
instance {p} : ToString (TestResult p) :=
  ⟨TestResult.toString⟩

#print SlimCheck.PrintableProp /-
/-- `printable_prop p` allows one to print a proposition so that
`slim_check` can indicate how values relate to each other.
-/
class PrintableProp (p : Prop) where
  printProp : Option String
#align slim_check.printable_prop SlimCheck.PrintableProp
-/

-- see [note priority]
instance (priority := 100) defaultPrintableProp {p} : PrintableProp p :=
  ⟨none⟩
#align slim_check.default_printable_prop SlimCheck.defaultPrintableProp

#print SlimCheck.Testable /-
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`run] [] -/
/-- `testable p` uses random examples to try to disprove `p`. -/
class Testable (p : Prop) where
  run (cfg : SlimCheckCfg) (minimize : Bool) : Gen (TestResult p)
#align slim_check.testable SlimCheck.Testable
-/

open _Root_.List

open TestResult

/-- applicative combinator proof carrying test results -/
def combine {p q : Prop} : PSum Unit (p → q) → PSum Unit p → PSum Unit q
  | PSum.inr f, PSum.inr x => PSum.inr (f x)
  | _, _ => PSum.inl ()
#align slim_check.combine SlimCheck.combine

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def andCounterExample {p q : Prop} : TestResult p → TestResult q → TestResult (p ∧ q)
  | failure Hce xs n, _ => failure (fun h => Hce h.1) xs n
  | _, failure Hce xs n => failure (fun h => Hce h.2) xs n
  | success xs, success ys => success <| combine (combine (PSum.inr And.intro) xs) ys
  | gave_up n, gave_up m => gave_up <| n + m
  | gave_up n, _ => gaveUp n
  | _, gave_up n => gaveUp n
#align slim_check.and_counter_example SlimCheck.andCounterExample

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction -/
def orCounterExample {p q : Prop} : TestResult p → TestResult q → TestResult (p ∨ q)
  | failure Hce xs n, failure Hce' ys n' =>
    failure (fun h => or_iff_not_and_not.1 h ⟨Hce, Hce'⟩) (xs ++ ys) (n + n')
  | success xs, _ => success <| combine (PSum.inr Or.inl) xs
  | _, success ys => success <| combine (PSum.inr Or.inr) ys
  | gave_up n, gave_up m => gave_up <| n + m
  | gave_up n, _ => gaveUp n
  | _, gave_up n => gaveUp n
#align slim_check.or_counter_example SlimCheck.orCounterExample

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def convertCounterExample {p q : Prop} (h : q → p) :
    TestResult p → optParam (PSum Unit (p → q)) (PSum.inl ()) → TestResult q
  | failure Hce xs n, _ => failure (mt h Hce) xs n
  | success Hp, Hpq => success (combine Hpq Hp)
  | gave_up n, _ => gaveUp n
#align slim_check.convert_counter_example SlimCheck.convertCounterExample

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def convertCounterExample' {p q : Prop} (h : p ↔ q) (r : TestResult p) : TestResult q :=
  convertCounterExample h.2 r (PSum.inr h.1)
#align slim_check.convert_counter_example' SlimCheck.convertCounterExample'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addToCounterExample (x : String) {p q : Prop} (h : q → p) :
    TestResult p → optParam (PSum Unit (p → q)) (PSum.inl ()) → TestResult q
  | failure Hce xs n, _ => failure (mt h Hce) (x::xs) n
  | r, hpq => convertCounterExample h r hpq
#align slim_check.add_to_counter_example SlimCheck.addToCounterExample

/-- Add some formatting to the information recorded by `add_to_counter_example`. -/
def addVarToCounterExample {γ : Type v} [Repr γ] (var : String) (x : γ) {p q : Prop} (h : q → p) :
    TestResult p → optParam (PSum Unit (p → q)) (PSum.inl ()) → TestResult q :=
  @addToCounterExample (var ++ " := " ++ repr x) _ _ h
#align slim_check.add_var_to_counter_example SlimCheck.addVarToCounterExample

#print SlimCheck.NamedBinder /-
/-- Gadget used to introspect the name of bound variables.

It is used with the `testable` typeclass so that
`testable (named_binder "x" (∀ x, p x))` can use the variable name
of `x` in error messages displayed to the user. If we find that instantiating
the above quantifier with 3 falsifies it, we can print:

```
==============
Problem found!
==============
x := 3
```
 -/
@[simp, nolint unused_arguments]
def NamedBinder (n : String) (p : Prop) : Prop :=
  p
#align slim_check.named_binder SlimCheck.NamedBinder
-/

/-- Is the given test result a failure? -/
def isFailure {p} : TestResult p → Bool
  | test_result.failure _ _ _ => true
  | _ => false
#align slim_check.is_failure SlimCheck.isFailure

instance andTestable (p q : Prop) [Testable p] [Testable q] : Testable (p ∧ q) :=
  ⟨fun cfg min => do
    let xp ← Testable.run p cfg min
    let xq ← Testable.run q cfg min
    pure <| and_counter_example xp xq⟩
#align slim_check.and_testable SlimCheck.andTestable

instance orTestable (p q : Prop) [Testable p] [Testable q] : Testable (p ∨ q) :=
  ⟨fun cfg min => do
    let xp ← Testable.run p cfg min
    match xp with
      | success (PSum.inl h) => pure <| success (PSum.inl h)
      | success (PSum.inr h) => pure <| success (PSum.inr <| Or.inl h)
      | _ => do
        let xq ← testable.run q cfg min
        pure <| or_counter_example xp xq⟩
#align slim_check.or_testable SlimCheck.orTestable

instance iffTestable (p q : Prop) [Testable (p ∧ q ∨ ¬p ∧ ¬q)] : Testable (p ↔ q) :=
  ⟨fun cfg min => do
    let xp ← Testable.run (p ∧ q ∨ ¬p ∧ ¬q) cfg min
    return <| convert_counter_example' (by tauto!) xp⟩
#align slim_check.iff_testable SlimCheck.iffTestable

open PrintableProp

instance (priority := 1000) decGuardTestable (p : Prop) [PrintableProp p] [Decidable p]
    (β : p → Prop) [∀ h, Testable (β h)] : Testable (NamedBinder var <| ∀ h, β h) :=
  ⟨fun cfg min => do
    if h : p then
        match print_prop p with
        | none =>
          (fun r => convert_counter_example (· <| h) r (PSum.inr fun q _ => q)) <$>
            testable.run (β h) cfg min
        | some str =>
          (fun r =>
              add_to_counter_example (s! "guard: {str}") (· <| h) r (PSum.inr fun q _ => q)) <$>
            testable.run (β h) cfg min
      else
        if cfg ∨ cfg then
          match print_prop p with
          | none => trace "discard" <| return <| gave_up 1
          | some str => (trace s! "discard: {str} does not hold") <| return <| gave_up 1
        else return <| gave_up 1⟩
#align slim_check.dec_guard_testable SlimCheck.decGuardTestable

/-- Type tag that replaces a type's `has_repr` instance with its `has_to_string` instance. -/
def UseHasToString (α : Type _) :=
  α
#align slim_check.use_has_to_string SlimCheck.UseHasToString

instance UseHasToString.inhabited [I : Inhabited α] : Inhabited (UseHasToString α) :=
  I
#align slim_check.use_has_to_string.inhabited SlimCheck.UseHasToString.inhabited

/-- Add the type tag `use_has_to_string` to an expression's type. -/
def UseHasToString.mk {α} (x : α) : UseHasToString α :=
  x
#align slim_check.use_has_to_string.mk SlimCheck.UseHasToString.mk

instance [ToString α] : Repr (UseHasToString α) :=
  ⟨@toString α _⟩

instance (priority := 2000) allTypesTestable [Testable (f ℤ)] :
    Testable (NamedBinder var <| ∀ x, f x) :=
  ⟨fun cfg min => do
    let r ← Testable.run (f ℤ) cfg min
    return <| add_var_to_counter_example var (use_has_to_string.mk "ℤ") (· <| ℤ) r⟩
#align slim_check.all_types_testable SlimCheck.allTypesTestable

/- warning: slim_check.trace_if_giveup -> SlimCheck.traceIfGiveup is a dubious translation:
lean 3 declaration is
  forall {p : Prop} {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Repr.{u_1} α], Bool -> String -> α -> (SlimCheck.TestResult p) -> (Thunkₓ.{u_2} β) -> β
but is expected to have type
  forall {p : Prop} {α : Type.{_aux_param_1}} {β : Type.{_aux_param_0}} [_inst_1 : Repr.{_aux_param_1} α], Bool -> String -> α -> (SlimCheck.TestResult p) -> (Thunkₓ.{_aux_param_0} β) -> β
Case conversion may be inaccurate. Consider using '#align slim_check.trace_if_giveup SlimCheck.traceIfGiveupₓ'. -/
/-- Trace the value of sampled variables if the sample is discarded. -/
def traceIfGiveup {p α β} [Repr α] (tracing_enabled : Bool) (var : String) (val : α) :
    TestResult p → Thunk β → β
  | test_result.gave_up _ => if tracing_enabled then trace s! " {var } := {repr val}" else (· <| ())
  | _ => (· <| ())
#align slim_check.trace_if_giveup SlimCheck.traceIfGiveup

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- testable instance for a property iterating over the element of a list -/
instance (priority := 5000) testForallInList [∀ x, Testable (β x)] [Repr α] :
    ∀ xs : List α, Testable (NamedBinder var <| ∀ x, NamedBinder var' <| x ∈ xs → β x)
  | [] =>
    ⟨fun tracing min =>
      return <|
        success <|
          PSum.inr
            (by
              introv x h
              cases h)⟩
  | x::xs =>
    ⟨fun cfg min => do
      let r ← Testable.run (β x) cfg min
      trace_if_giveup cfg var x r <|
          match r with
          | failure _ _ _ =>
            return <|
              add_var_to_counter_example var x
                (by
                  intro h
                  apply h
                  left
                  rfl)
                r
          | success hp => do
            let rs ← @testable.run _ (test_forall_in_list xs) cfg min
            return <|
                convert_counter_example
                  (by
                    intro h i h'
                    apply h
                    right
                    apply h')
                  rs
                  (combine
                    (PSum.inr <| by
                      intro j h
                      simp only [ball_cons, named_binder]
                      constructor <;> assumption)
                    hp)
          | gave_up n => do
            let rs ← @testable.run _ (test_forall_in_list xs) cfg min
            match rs with
              | success _ => return <| gave_up n
              | failure Hce xs n =>
                return <|
                  failure
                    (by
                      simp only [ball_cons, named_binder]
                      apply not_and_of_not_right _ Hce)
                    xs n
              | gave_up n' => return <| gave_up (n + n')⟩
#align slim_check.test_forall_in_list SlimCheck.testForallInList

/-- Test proposition `p` by randomly selecting one of the provided
testable instances. -/
def combineTestable (p : Prop) (t : List <| Testable p) (h : 0 < t.length) : Testable p :=
  ⟨fun cfg min =>
    have : 0 < length (map (fun t => @Testable.run _ t cfg min) t) := by
      rw [length_map]
      apply h
    Gen.oneOf (List.map (fun t => @Testable.run _ t cfg min) t) this⟩
#align slim_check.combine_testable SlimCheck.combineTestable

open SampleableExt

/-- Format the counter-examples found in a test failure.
-/
def formatFailure (s : String) (xs : List String) (n : ℕ) : String :=
  let counter_ex := String.intercalate "\n" xs
  s! "
    ===================
    {s }
    
    {counter_ex }
    ({n} shrinks)
    -------------------
    "
#align slim_check.format_failure SlimCheck.formatFailure

/-- Format the counter-examples found in a test failure.
-/
def formatFailure' (s : String) {p} : TestResult p → String
  | success a => ""
  | gave_up a => ""
  | test_result.failure _ xs n => formatFailure s xs n
#align slim_check.format_failure' SlimCheck.formatFailure'

/-- Increase the number of shrinking steps in a test result.
-/
def addShrinks {p} (n : ℕ) : TestResult p → TestResult p
  | r@(success a) => r
  | r@(gave_up a) => r
  | test_result.failure h vs n' => TestResult.failure h vs <| n + n'
#align slim_check.add_shrinks SlimCheck.addShrinks

/-- Shrink a counter-example `x` by using `shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.

The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `sizeof`)
than `x`. -/
def minimizeAux [SampleableExt α] [∀ x, Testable (β x)] (cfg : SlimCheckCfg) (var : String) :
    ProxyRepr α → ℕ → OptionT Gen (Σx, TestResult (β (interp α x))) :=
  (WellFounded.fix WellFoundedRelation.wf) fun x f_rec n => do
    if cfg then
        return <|
          trace
            (s! "candidates for {var } :=
              {repr (sampleable_ext.shrink x).toList}
              ")
            ()
      else pure ()
    let ⟨y, r, ⟨h₁⟩⟩ ←
      (SampleableExt.shrink x).mfirst fun ⟨a, h⟩ => do
          let ⟨r⟩ ←
            monadLift
                (Uliftable.up <| Testable.run (β (interp α a)) cfg true :
                  Gen (ULift <| test_result <| β <| interp α a))
          if is_failure r then
              pure (⟨a, r, ⟨h⟩⟩ : Σa, test_result (β (interp α a)) × PLift (sizeof_lt a x))
            else failure
    if cfg then
        return <|
          trace ((s! "{var } := {repr y}") ++ format_failure' "Shrink counter-example:" r) ()
      else pure ()
    f_rec y h₁ (n + 1) <|> pure ⟨y, add_shrinks (n + 1) r⟩
#align slim_check.minimize_aux SlimCheck.minimizeAux

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExt α] [∀ x, Testable (β x)] (cfg : SlimCheckCfg) (var : String)
    (x : ProxyRepr α) (r : TestResult (β (interp α x))) : Gen (Σx, TestResult (β (interp α x))) :=
  do
  if cfg then
      return <| trace ((s! "{var } := {repr x}") ++ format_failure' "Shrink counter-example:" r) ()
    else pure ()
  let x' ← OptionT.run <| minimizeAux α _ cfg var x 0
  pure <| x' ⟨x, r⟩
#align slim_check.minimize SlimCheck.minimize

instance (priority := 2000) existsTestable (p : Prop)
    [Testable (NamedBinder var (∀ x, NamedBinder var' <| β x → p))] :
    Testable (NamedBinder var' (NamedBinder var (∃ x, β x) → p)) :=
  ⟨fun cfg min => do
    let x ← Testable.run (NamedBinder var (∀ x, NamedBinder var' <| β x → p)) cfg min
    pure <| convert_counter_example' exists_imp x⟩
#align slim_check.exists_testable SlimCheck.existsTestable

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it -/
instance varTestable [SampleableExt α] [∀ x, Testable (β x)] :
    Testable (NamedBinder var <| ∀ x : α, β x) :=
  ⟨fun cfg min => do
    (Uliftable.adaptDown (sampleable_ext.sample α)) fun x => do
        let r ← testable.run (β (sampleable_ext.interp α x)) cfg ff
        (Uliftable.adaptDown
              (if is_failure r ∧ min then minimize _ _ cfg var x r
              else if cfg then (trace s! "  {var } := {repr x}") <| pure ⟨x, r⟩ else pure ⟨x, r⟩))
            fun ⟨x, r⟩ =>
            return <|
              trace_if_giveup cfg var x r
                (add_var_to_counter_example var x (· <| sampleable_ext.interp α x) r)⟩
#align slim_check.var_testable SlimCheck.varTestable

/-- Test a universal property about propositions -/
instance propVarTestable (β : Prop → Prop) [I : ∀ b : Bool, Testable (β b)] :
    Testable (NamedBinder var <| ∀ p : Prop, β p) :=
  ⟨fun cfg min => do
    (convert_counter_example fun h (b : Bool) => h b) <$>
        @testable.run (named_binder var <| ∀ b : Bool, β b) _ cfg min⟩
#align slim_check.prop_var_testable SlimCheck.propVarTestable

instance (priority := 3000) unusedVarTestable (β) [Inhabited α] [Testable β] :
    Testable (NamedBinder var <| ∀ x : α, β) :=
  ⟨fun cfg min => do
    let r ← Testable.run β cfg min
    pure <| convert_counter_example (· <| default) r (PSum.inr fun x _ => x)⟩
#align slim_check.unused_var_testable SlimCheck.unusedVarTestable

instance (priority := 2000) subtypeVarTestable {p : α → Prop} [∀ x, PrintableProp (p x)]
    [∀ x, Testable (β x)] [I : SampleableExt (Subtype p)] :
    Testable (NamedBinder var <| ∀ x : α, NamedBinder var' <| p x → β x) :=
  ⟨fun cfg min => do
    let test (x : Subtype p) : Testable (β x) :=
      ⟨fun cfg min => do
        let r ← Testable.run (β x.val) cfg min
        match print_prop (p x) with
          | none => pure r
          | some str =>
            pure <| add_to_counter_example (s! "guard: {str} (by construction)") id r (PSum.inr id)⟩
    let r ← @Testable.run (∀ x : Subtype p, β x.val) (@SlimCheck.varTestable var _ _ I test) cfg min
    pure <|
        convert_counter_example'
          ⟨fun (h : ∀ x : Subtype p, β x) x h' => h ⟨x, h'⟩, fun h ⟨x, h'⟩ => h x h'⟩ r⟩
#align slim_check.subtype_var_testable SlimCheck.subtypeVarTestable

instance (priority := 100) decidableTestable (p : Prop) [PrintableProp p] [Decidable p] :
    Testable p :=
  ⟨fun cfg min =>
    return <|
      if h : p then success (PSum.inr h)
      else
        match printProp p with
        | none => failure h [] 0
        | some str => failure h [s! "issue: {str} does not hold"] 0⟩
#align slim_check.decidable_testable SlimCheck.decidableTestable

#print SlimCheck.Eq.printableProp /-
instance Eq.printableProp {α} [Repr α] (x y : α) : PrintableProp (x = y) :=
  ⟨some s!"{(repr x)} = {repr y}"⟩
#align slim_check.eq.printable_prop SlimCheck.Eq.printableProp
-/

#print SlimCheck.Ne.printableProp /-
instance Ne.printableProp {α} [Repr α] (x y : α) : PrintableProp (x ≠ y) :=
  ⟨some s!"{(repr x)} ≠ {repr y}"⟩
#align slim_check.ne.printable_prop SlimCheck.Ne.printableProp
-/

instance Le.printableProp {α} [LE α] [Repr α] (x y : α) : PrintableProp (x ≤ y) :=
  ⟨some s!"{(repr x)} ≤ {repr y}"⟩
#align slim_check.le.printable_prop SlimCheck.Le.printableProp

instance Lt.printableProp {α} [LT α] [Repr α] (x y : α) : PrintableProp (x < y) :=
  ⟨some s!"{(repr x)} < {repr y}"⟩
#align slim_check.lt.printable_prop SlimCheck.Lt.printableProp

instance Perm.printableProp {α} [Repr α] (xs ys : List α) : PrintableProp (xs ~ ys) :=
  ⟨some s!"{(repr xs)} ~ {repr ys}"⟩
#align slim_check.perm.printable_prop SlimCheck.Perm.printableProp

#print SlimCheck.And.printableProp /-
instance And.printableProp (x y : Prop) [PrintableProp x] [PrintableProp y] :
    PrintableProp (x ∧ y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } ∧ {y'})"⟩
#align slim_check.and.printable_prop SlimCheck.And.printableProp
-/

#print SlimCheck.Or.printableProp /-
instance Or.printableProp (x y : Prop) [PrintableProp x] [PrintableProp y] :
    PrintableProp (x ∨ y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } ∨ {y'})"⟩
#align slim_check.or.printable_prop SlimCheck.Or.printableProp
-/

#print SlimCheck.Iff.printableProp /-
instance Iff.printableProp (x y : Prop) [PrintableProp x] [PrintableProp y] :
    PrintableProp (x ↔ y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } ↔ {y'})"⟩
#align slim_check.iff.printable_prop SlimCheck.Iff.printableProp
-/

#print SlimCheck.Imp.printableProp /-
instance Imp.printableProp (x y : Prop) [PrintableProp x] [PrintableProp y] :
    PrintableProp (x → y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } → {y'})"⟩
#align slim_check.imp.printable_prop SlimCheck.Imp.printableProp
-/

#print SlimCheck.Not.printableProp /-
instance Not.printableProp (x : Prop) [PrintableProp x] : PrintableProp ¬x :=
  ⟨do
    let x' ← printProp x
    some s! "¬ {x'}"⟩
#align slim_check.not.printable_prop SlimCheck.Not.printableProp
-/

#print SlimCheck.True.printableProp /-
instance True.printableProp : PrintableProp True :=
  ⟨some "true"⟩
#align slim_check.true.printable_prop SlimCheck.True.printableProp
-/

#print SlimCheck.False.printableProp /-
instance False.printableProp : PrintableProp False :=
  ⟨some "false"⟩
#align slim_check.false.printable_prop SlimCheck.False.printableProp
-/

#print SlimCheck.Bool.printableProp /-
instance Bool.printableProp (b : Bool) : PrintableProp b :=
  ⟨some <| if b then "true" else "false"⟩
#align slim_check.bool.printable_prop SlimCheck.Bool.printableProp
-/

section Io

open _Root_.Nat

variable {p : Prop}

#print SlimCheck.retry /-
/-- Execute `cmd` and repeat every time the result is `gave_up` (at most
`n` times). -/
def retry (cmd : Rand (TestResult p)) : ℕ → Rand (TestResult p)
  | 0 => return <| gaveUp 1
  | succ n => do
    let r ← cmd
    match r with
      | success hp => return <| success hp
      | failure Hce xs n => return (failure Hce xs n)
      | gave_up _ => retry n
#align slim_check.retry SlimCheck.retry
-/

#print SlimCheck.giveUp /-
/-- Count the number of times the test procedure gave up. -/
def giveUp (x : ℕ) : TestResult p → TestResult p
  | success (PSum.inl ()) => gaveUp x
  | success (PSum.inr p) => success (PSum.inr p)
  | gave_up n => gaveUp (n + x)
  | failure Hce xs n => failure Hce xs n
#align slim_check.give_up SlimCheck.giveUp
-/

variable (p)

variable [Testable p]

/- warning: slim_check.testable.run_suite_aux -> SlimCheck.Testable.runSuiteAux is a dubious translation:
lean 3 declaration is
  forall (p : Prop) [_inst_1 : SlimCheck.Testable p], SlimCheck.SlimCheckCfg -> (SlimCheck.TestResult p) -> Nat -> (Rand.{0} (SlimCheck.TestResult p))
but is expected to have type
  forall (p : Prop) [inst._@.Mathlib.Testing.SlimCheck.Testable._hyg.5508 : SlimCheck.Testable p], SlimCheck.Configuration -> (SlimCheck.TestResult p) -> Nat -> (Rand.{0} (SlimCheck.TestResult p))
Case conversion may be inaccurate. Consider using '#align slim_check.testable.run_suite_aux SlimCheck.Testable.runSuiteAuxₓ'. -/
/-- Try `n` times to find a counter-example for `p`. -/
def Testable.runSuiteAux (cfg : SlimCheckCfg) : TestResult p → ℕ → Rand (TestResult p)
  | r, 0 => return r
  | r, succ n => do
    let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    when cfg <| return <| trace s!"[slim_check: sample]" ()
    let x ← retry ((Testable.run p cfg true).run ⟨size⟩) 10
    match x with
      | success (PSum.inl ()) => testable.run_suite_aux r n
      | success (PSum.inr Hp) => return <| success (PSum.inr Hp)
      | failure Hce xs n => return (failure Hce xs n)
      | gave_up g => testable.run_suite_aux (give_up g r) n
#align slim_check.testable.run_suite_aux SlimCheck.Testable.runSuiteAux

/- warning: slim_check.testable.run_suite -> SlimCheck.Testable.runSuite is a dubious translation:
lean 3 declaration is
  forall (p : Prop) [_inst_1 : SlimCheck.Testable p], (optParam.{1} SlimCheck.SlimCheckCfg (SlimCheck.SlimCheckCfg.mk (OfNat.ofNat.{0} Nat 100 (OfNat.mk.{0} Nat 100 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))) (OfNat.ofNat.{0} Nat 100 (OfNat.mk.{0} Nat 100 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))) Bool.false Bool.false Bool.false Bool.false (Option.none.{0} Nat) Bool.false)) -> (Rand.{0} (SlimCheck.TestResult p))
but is expected to have type
  forall (p : Prop) [inst._@.Mathlib.Testing.SlimCheck.Testable._hyg.5786 : SlimCheck.Testable p], (optParam.{1} SlimCheck.Configuration (SlimCheck.Configuration.mk ([mdata structInstDefault:1 OfNat.ofNat.{0} Nat 100 (instOfNatNat 100)]) ([mdata structInstDefault:1 OfNat.ofNat.{0} Nat 100 (instOfNatNat 100)]) ([mdata structInstDefault:1 OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Option.none.{0} Nat]) ([mdata structInstDefault:1 Bool.false]))) -> (Rand.{0} (SlimCheck.TestResult p))
Case conversion may be inaccurate. Consider using '#align slim_check.testable.run_suite SlimCheck.Testable.runSuiteₓ'. -/
/-- Try to find a counter-example of `p`. -/
def Testable.runSuite (cfg : SlimCheckCfg := {  }) : Rand (TestResult p) :=
  Testable.runSuiteAux p cfg (success <| PSum.inl ()) cfg.numInst
#align slim_check.testable.run_suite SlimCheck.Testable.runSuite

/-- Run a test suite for `p` in `io`. -/
def Testable.check' (cfg : SlimCheckCfg := {  }) : Io (TestResult p) :=
  match cfg.randomSeed with
  | some seed => Io.runRandWith seed (Testable.runSuite p cfg)
  | none => Io.runRand (Testable.runSuite p cfg)
#align slim_check.testable.check' SlimCheck.Testable.check'

namespace Tactic

open _Root_.Tactic Expr

/-!
## Decorations

Instances of `testable` use `named_binder` as a decoration on
propositions in order to access the name of bound variables, as in
`named_binder "x" (forall x, x < y)`.  This helps the
`testable` instances create useful error messages where variables
are matched with values that falsify a given proposition.

The following functions help support the gadget so that the user does
not have to put them in themselves.
-/


/-- `add_existential_decorations p` adds `a `named_binder` annotation at the
root of `p` if `p` is an existential quantification. -/
unsafe def add_existential_decorations : expr → expr
  | e@q(@Exists $(α) $(lam n bi d b)) =>
    let n := toString n
    const `` named_binder [] (q(n) : expr) e
  | e => e
#align slim_check.tactic.add_existential_decorations slim_check.tactic.add_existential_decorations

/-- Traverse the syntax of a proposition to find universal quantifiers
and existential quantifiers and add `named_binder` annotations next to
them. -/
unsafe def add_decorations : expr → expr
  | e =>
    e.replace fun e _ =>
      match e with
      | pi n bi d b =>
        let n := toString n
        some <|
          const `` named_binder [] (q(n) : expr)
            (pi n bi (add_existential_decorations d) (add_decorations b))
      | e => none
#align slim_check.tactic.add_decorations slim_check.tactic.add_decorations

/-- `decorations_of p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
@[reducible, nolint unused_arguments]
def DecorationsOf (p : Prop) :=
  Prop
#align slim_check.tactic.decorations_of SlimCheck.Tactic.DecorationsOf

/-- In a goal of the shape `⊢ tactic.decorations_of p`, `mk_decoration` examines
the syntax of `p` and add `named_binder` around universal quantifications and
existential quantifications to improve error messages.

This tool can be used in the declaration of a function as follows:

```lean
def foo (p : Prop) (p' : tactic.decorations_of p . mk_decorations) [testable p'] : ...
```

`p` is the parameter given by the user, `p'` is an equivalent proposition where
the quantifiers are annotated with `named_binder`.
-/
unsafe def mk_decorations : tactic Unit := do
  let q(Tactic.DecorationsOf $(p)) ← target
  exact <| add_decorations p
#align slim_check.tactic.mk_decorations slim_check.tactic.mk_decorations

end Tactic

/- warning: slim_check.testable.check -> SlimCheck.Testable.check is a dubious translation:
lean 3 declaration is
  forall (p : Prop), (optParam.{1} SlimCheck.SlimCheckCfg (SlimCheck.SlimCheckCfg.mk (OfNat.ofNat.{0} Nat 100 (OfNat.mk.{0} Nat 100 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))) (OfNat.ofNat.{0} Nat 100 (OfNat.mk.{0} Nat 100 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))) Bool.false Bool.false Bool.false Bool.false (Option.none.{0} Nat) Bool.false)) -> (forall (p' : autoParamₓ.{1} (SlimCheck.Tactic.DecorationsOf p) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 109 (OfNat.mk.{0} Nat 109 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 107 (OfNat.mk.{0} Nat 107 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 95 (OfNat.mk.{0} Nat 95 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 100 (OfNat.mk.{0} Nat 100 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 109 (OfNat.mk.{0} Nat 109 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 95 (OfNat.mk.{0} Nat 95 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 104 (OfNat.mk.{0} Nat 104 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 107 (OfNat.mk.{0} Nat 107 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)))) [_inst_2 : SlimCheck.Testable p'], Io PUnit.{1})
but is expected to have type
  forall (p : Prop), (optParam.{1} SlimCheck.Configuration (SlimCheck.Configuration.mk ([mdata structInstDefault:1 OfNat.ofNat.{0} Nat 100 (instOfNatNat 100)]) ([mdata structInstDefault:1 OfNat.ofNat.{0} Nat 100 (instOfNatNat 100)]) ([mdata structInstDefault:1 OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Bool.false]) ([mdata structInstDefault:1 Option.none.{0} Nat]) ([mdata structInstDefault:1 Bool.false]))) -> (forall (p' : autoParam.{1} (SlimCheck.Decorations.DecorationsOf p) _auto._@.Mathlib.Testing.SlimCheck.Testable._hyg.6230) [inst._@.Mathlib.Testing.SlimCheck.Testable._hyg.6263 : SlimCheck.Testable p'], IO PUnit.{1})
Case conversion may be inaccurate. Consider using '#align slim_check.testable.check SlimCheck.Testable.checkₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:61:18: unsupported non-interactive tactic tactic.mk_decorations -/
/-- Run a test suite for `p` and return true or false: should we believe that `p` holds? -/
def Testable.check (p : Prop) (cfg : SlimCheckCfg := {  })
    (p' : Tactic.DecorationsOf p := by
      run_tac
        tactic.mk_decorations)
    [Testable p'] : Io PUnit := do
  let x ←
    match cfg.randomSeed with
      | some seed => Io.runRandWith seed (Testable.runSuite p' cfg)
      | none => Io.runRand (Testable.runSuite p' cfg)
  match x with
    | success _ => when ¬cfg <| Io.putStrLn "Success"
    | gave_up n => Io.fail s! "Gave up {repr n} times"
    | failure _ xs n => do
      Io.fail <| format_failure "Found problems!" xs n
#align slim_check.testable.check SlimCheck.Testable.check

end Io

end SlimCheck

