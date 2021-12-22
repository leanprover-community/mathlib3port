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

variable (var var' : Stringₓ)

variable (α : Type u)

variable (β : α → Prop)

variable (f : Type → Prop)

namespace SlimCheck

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler inhabited
/--  Result of trying to disprove `p`

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
inductive test_result (p : Prop)
  | success : Psum Unit p → test_result
  | gave_up {} : ℕ → test_result
  | failure : ¬p → List Stringₓ → ℕ → test_result
  deriving [anonymous]

/--  format a `test_result` as a string. -/
protected def test_result.to_string {p} : test_result p → Stringₓ
  | test_result.success (Psum.inl ()) => "success (without proof)"
  | test_result.success (Psum.inr h) => "success (with proof)"
  | test_result.gave_up n => s! "gave up {n} times"
  | test_result.failure a vs _ => s! "failed {vs}"

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler has_reflect
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler inhabited
/--  configuration for testing a property -/
structure slim_check_cfg where
  numInst : ℕ := 100
  maxSize : ℕ := 100
  traceDiscarded : Bool := ff
  traceSuccess : Bool := ff
  traceShrink : Bool := ff
  traceShrinkCandidates : Bool := ff
  randomSeed : Option ℕ := none
  quiet : Bool := ff
  deriving [anonymous], [anonymous]

instance {p} : HasToString (test_result p) :=
  ⟨test_result.to_string⟩

/-- 
`printable_prop p` allows one to print a proposition so that
`slim_check` can indicate how values relate to each other.
-/
class printable_prop (p : Prop) where
  printProp : Option Stringₓ

instance (priority := 100) default_printable_prop {p} : printable_prop p :=
  ⟨none⟩

/--  `testable p` uses random examples to try to disprove `p`. -/
class testable (p : Prop) where
  run {} (cfg : slim_check_cfg) (minimize : Bool) : gen (test_result p)

open _Root_.List

open TestResult

/--  applicative combinator proof carrying test results -/
def combine {p q : Prop} : Psum Unit (p → q) → Psum Unit p → Psum Unit q
  | Psum.inr f, Psum.inr x => Psum.inr (f x)
  | _, _ => Psum.inl ()

/--  Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and_counter_example {p q : Prop} : test_result p → test_result q → test_result (p ∧ q)
  | failure Hce xs n, _ => failure (fun h => Hce h.1) xs n
  | _, failure Hce xs n => failure (fun h => Hce h.2) xs n
  | success xs, success ys => success $ combine (combine (Psum.inr And.intro) xs) ys
  | gave_up n, gave_up m => gave_up $ n+m
  | gave_up n, _ => gave_up n
  | _, gave_up n => gave_up n

/--  Combine the test result for properties `p` and `q` to create a test for their disjunction -/
def or_counter_example {p q : Prop} : test_result p → test_result q → test_result (p ∨ q)
  | failure Hce xs n, failure Hce' ys n' => failure (fun h => or_iff_not_and_not.1 h ⟨Hce, Hce'⟩) (xs ++ ys) (n+n')
  | success xs, _ => success $ combine (Psum.inr Or.inl) xs
  | _, success ys => success $ combine (Psum.inr Or.inr) ys
  | gave_up n, gave_up m => gave_up $ n+m
  | gave_up n, _ => gave_up n
  | _, gave_up n => gave_up n

/--  If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def convert_counter_example {p q : Prop} (h : q → p) :
    test_result p → optParam (Psum Unit (p → q)) (Psum.inl ()) → test_result q
  | failure Hce xs n, _ => failure (mt h Hce) xs n
  | success Hp, Hpq => success (combine Hpq Hp)
  | gave_up n, _ => gave_up n

/--  Test `q` by testing `p` and proving the equivalence between the two. -/
def convert_counter_example' {p q : Prop} (h : p ↔ q) (r : test_result p) : test_result q :=
  convert_counter_example h.2 r (Psum.inr h.1)

/--  When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def add_to_counter_example (x : Stringₓ) {p q : Prop} (h : q → p) :
    test_result p → optParam (Psum Unit (p → q)) (Psum.inl ()) → test_result q
  | failure Hce xs n, _ => failure (mt h Hce) (x :: xs) n
  | r, hpq => convert_counter_example h r hpq

/--  Add some formatting to the information recorded by `add_to_counter_example`. -/
def add_var_to_counter_example {γ : Type v} [HasRepr γ] (var : Stringₓ) (x : γ) {p q : Prop} (h : q → p) :
    test_result p → optParam (Psum Unit (p → q)) (Psum.inl ()) → test_result q :=
  @add_to_counter_example (var ++ " := " ++ reprₓ x) _ _ h

/--  Gadget used to introspect the name of bound variables.

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
def named_binder (n : Stringₓ) (p : Prop) : Prop :=
  p

/--  Is the given test result a failure? -/
def is_failure {p} : test_result p → Bool
  | test_result.failure _ _ _ => tt
  | _ => ff

instance and_testable (p q : Prop) [testable p] [testable q] : testable (p ∧ q) :=
  ⟨fun cfg min => do
    let xp ← testable.run p cfg min
    let xq ← testable.run q cfg min
    pure $ and_counter_example xp xq⟩

instance or_testable (p q : Prop) [testable p] [testable q] : testable (p ∨ q) :=
  ⟨fun cfg min => do
    let xp ← testable.run p cfg min
    match xp with
      | success (Psum.inl h) => pure $ success (Psum.inl h)
      | success (Psum.inr h) => pure $ success (Psum.inr $ Or.inl h)
      | _ => do
        let xq ← testable.run q cfg min
        pure $ or_counter_example xp xq⟩

instance iff_testable (p q : Prop) [testable (p ∧ q ∨ ¬p ∧ ¬q)] : testable (p ↔ q) :=
  ⟨fun cfg min => do
    let xp ← testable.run (p ∧ q ∨ ¬p ∧ ¬q) cfg min
    return $
        convert_counter_example'
          (by
            tauto!)
          xp⟩

open PrintableProp

instance (priority := 1000) dec_guard_testable (p : Prop) [printable_prop p] [Decidable p] (β : p → Prop)
    [∀ h, testable (β h)] : testable (named_binder var $ ∀ h, β h) :=
  ⟨fun cfg min => do
    if h : p then
        match print_prop p with
        | none => (fun r => convert_counter_example (· $ h) r (Psum.inr $ fun q _ => q)) <$> testable.run (β h) cfg min
        | some str =>
          (fun r => add_to_counter_example (s! "guard: {str}") (· $ h) r (Psum.inr $ fun q _ => q)) <$>
            testable.run (β h) cfg min
      else
        if cfg.trace_discarded ∨ cfg.trace_success then
          match print_prop p with
          | none => trace "discard" $ return $ gave_up 1
          | some str => (trace s! "discard: {str} does not hold") $ return $ gave_up 1
        else return $ gave_up 1⟩

/--  Type tag that replaces a type's `has_repr` instance with its `has_to_string` instance. -/
def use_has_to_string (α : Type _) :=
  α

instance use_has_to_string.inhabited [I : Inhabited α] : Inhabited (use_has_to_string α) :=
  I

/--  Add the type tag `use_has_to_string` to an expression's type. -/
def use_has_to_string.mk {α} (x : α) : use_has_to_string α :=
  x

instance [HasToString α] : HasRepr (use_has_to_string α) :=
  ⟨@toString α _⟩

instance (priority := 2000) all_types_testable [testable (f ℤ)] : testable (named_binder var $ ∀ x, f x) :=
  ⟨fun cfg min => do
    let r ← testable.run (f ℤ) cfg min
    return $ add_var_to_counter_example var (use_has_to_string.mk "ℤ") (· $ ℤ) r⟩

/--  Trace the value of sampled variables if the sample is discarded. -/
def trace_if_giveup {p α β} [HasRepr α] (tracing_enabled : Bool) (var : Stringₓ) (val : α) :
    test_result p → Thunkₓ β → β
  | test_result.gave_up _ => if tracing_enabled then trace s! " {var } := {reprₓ val}" else · $ ()
  | _ => · $ ()

-- failed to format: format: uncaught backtrack exception
/-- testable instance for a property iterating over the element of a list -/
  instance
    ( priority := 5000 )
    test_forall_in_list
    [ ∀ x , testable ( β x ) ] [ HasRepr α ]
      : ∀ xs : List α , testable ( named_binder var $ ∀ x , named_binder var' $ x ∈ xs → β x )
    | [ ] => ⟨ fun tracing min => return $ success $ Psum.inr ( by introv x h cases h ) ⟩
      |
        x :: xs
        =>
        ⟨
          fun
            cfg min
              =>
              do
                let r ← testable.run ( β x ) cfg min
                  trace_if_giveup cfg.trace_discarded var x r
                    $
                    match
                      r
                      with
                      | failure _ _ _ => return $ add_var_to_counter_example var x ( by intro h apply h left rfl ) r
                        |
                          success hp
                          =>
                          do
                            let rs ← @ testable.run _ ( test_forall_in_list xs ) cfg min
                              return
                                $
                                convert_counter_example
                                  ( by intro h i h' apply h right apply h' )
                                    rs
                                    (
                                      combine
                                        (
                                            Psum.inr
                                              $
                                              by
                                                intro j h
                                                  simp only [ ball_cons , named_binder ]
                                                  constructor <;> assumption
                                            )
                                          hp
                                      )
                        |
                          gave_up n
                          =>
                          do
                            let rs ← @ testable.run _ ( test_forall_in_list xs ) cfg min
                              match
                                rs
                                with
                                | success _ => return $ gave_up n
                                  |
                                    failure Hce xs n
                                    =>
                                    return
                                      $
                                      failure
                                        ( by simp only [ ball_cons , named_binder ] apply not_and_of_not_right _ Hce )
                                          xs
                                          n
                                  | gave_up n' => return $ gave_up ( n + n' )
          ⟩

/--  Test proposition `p` by randomly selecting one of the provided
testable instances. -/
def combine_testable (p : Prop) (t : List $ testable p) (h : 0 < t.length) : testable p :=
  ⟨fun cfg min =>
    have : 0 < length (map (fun t => @testable.run _ t cfg min) t) := by
      rw [length_map]
      apply h
    gen.one_of (List.map (fun t => @testable.run _ t cfg min) t) this⟩

open SampleableExt

/-- 
Format the counter-examples found in a test failure.
-/
def format_failure (s : Stringₓ) (xs : List Stringₓ) (n : ℕ) : Stringₓ :=
  let counter_ex := Stringₓ.intercalate "\n" xs
  s! "
    ===================
    {s }
    
    {counter_ex }
    ({n} shrinks)
    -------------------
    "

/-- 
Format the counter-examples found in a test failure.
-/
def format_failure' (s : Stringₓ) {p} : test_result p → Stringₓ
  | success a => ""
  | gave_up a => ""
  | test_result.failure _ xs n => format_failure s xs n

/-- 
Increase the number of shrinking steps in a test result.
-/
def add_shrinks {p} (n : ℕ) : test_result p → test_result p
  | r@(success a) => r
  | r@(gave_up a) => r
  | test_result.failure h vs n' => test_result.failure h vs $ n+n'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Shrink a counter-example `x` by using `shrink x`, picking the first\ncandidate that falsifies a property and recursively shrinking that one.\n\nThe process is guaranteed to terminate because `shrink x` produces\na proof that all the values it produces are smaller (according to `sizeof`)\nthan `x`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `minimize_aux [])
  (Command.optDeclSig
   [(Term.instBinder "[" [] (Term.app `sampleable_ext [`α]) "]")
    (Term.instBinder
     "["
     []
     (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `testable [(Term.app `β [`x])]))
     "]")
    (Term.explicitBinder "(" [`cfg] [":" `slim_check_cfg] [] ")")
    (Term.explicitBinder "(" [`var] [":" `Stringₓ] [] ")")]
   [(Term.typeSpec
     ":"
     (Term.arrow
      (Term.app `proxy_repr [`α])
      "→"
      (Term.arrow
       (termℕ "ℕ")
       "→"
       (Term.app
        `OptionTₓ
        [`gen
         (Init.Data.Sigma.Basic.«termΣ_,_»
          "Σ"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          ", "
          (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `x])])]))]))))])
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app `WellFounded.fix [`HasWellFounded.wf])
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x `f_rec `n] [])]
      "=>"
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `cfg.trace_shrink_candidates
            "then"
            («term_$__»
             `return
             "$"
             (Term.app
              `trace
              [(termS!_
                "s!"
                (interpolatedStrKind
                 (interpolatedStrLitKind "\"candidates for {")
                 `var
                 (interpolatedStrLitKind "} :=\n{")
                 (Term.app `reprₓ [(Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `toList)])
                 (interpolatedStrLitKind "}\n\"")))
               (Term.paren "(" [] ")")]))
            "else"
            (Term.app `pure [(Term.paren "(" [] ")")])))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.anonymousCtor "⟨" [`y "," `r "," (Term.anonymousCtor "⟨" [`h₁] "⟩")] "⟩")
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `mfirst)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                 "=>"
                 (Term.do
                  "do"
                  (Term.doSeqIndent
                   [(Term.doSeqItem
                     (Term.doLetArrow
                      "let"
                      []
                      (Term.doPatDecl
                       (Term.anonymousCtor "⟨" [`r] "⟩")
                       "←"
                       (Term.doExpr
                        (Term.app
                         `monad_lift
                         [(Term.paren
                           "("
                           [(«term_$__»
                             `Uliftable.up
                             "$"
                             (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
                            [(Term.typeAscription
                              ":"
                              (Term.app
                               `gen
                               [(«term_$__»
                                 `Ulift
                                 "$"
                                 («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
                           ")")]))
                       []))
                     [])
                    (Term.doSeqItem
                     (Term.doExpr
                      (termIfThenElse
                       "if"
                       (Term.app `is_failure [`r])
                       "then"
                       (Term.app
                        `pure
                        [(Term.paren
                          "("
                          [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
                           [(Term.typeAscription
                             ":"
                             (Init.Data.Sigma.Basic.«termΣ_,_»
                              "Σ"
                              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                              ", "
                              («term_×_»
                               (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                               "×"
                               (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
                          ")")])
                       "else"
                       `failure))
                     [])]))))]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            `cfg.trace_shrink
            "then"
            («term_$__»
             `return
             "$"
             (Term.app
              `trace
              [(«term_++_»
                (termS!_
                 "s!"
                 (interpolatedStrKind
                  (interpolatedStrLitKind "\"{")
                  `var
                  (interpolatedStrLitKind "} := {")
                  (Term.app `reprₓ [`y])
                  (interpolatedStrLitKind "}\"")))
                "++"
                (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
               (Term.paren "(" [] ")")]))
            "else"
            (Term.app `pure [(Term.paren "(" [] ")")])))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Init.Control.Alternative.«term_<|>_»
            (Term.app `f_rec [`y `h₁ (Init.Logic.«term_+_» `n "+" (numLit "1"))])
            " <|> "
            (Term.app
             `pure
             [(Term.anonymousCtor
               "⟨"
               [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])]
               "⟩")])))
          [])])))))
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
  («term_$__»
   (Term.app `WellFounded.fix [`HasWellFounded.wf])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x `f_rec `n] [])]
     "=>"
     (Term.do
      "do"
      (Term.doSeqIndent
       [(Term.doSeqItem
         (Term.doExpr
          (termIfThenElse
           "if"
           `cfg.trace_shrink_candidates
           "then"
           («term_$__»
            `return
            "$"
            (Term.app
             `trace
             [(termS!_
               "s!"
               (interpolatedStrKind
                (interpolatedStrLitKind "\"candidates for {")
                `var
                (interpolatedStrLitKind "} :=\n{")
                (Term.app `reprₓ [(Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `toList)])
                (interpolatedStrLitKind "}\n\"")))
              (Term.paren "(" [] ")")]))
           "else"
           (Term.app `pure [(Term.paren "(" [] ")")])))
         [])
        (Term.doSeqItem
         (Term.doLetArrow
          "let"
          []
          (Term.doPatDecl
           (Term.anonymousCtor "⟨" [`y "," `r "," (Term.anonymousCtor "⟨" [`h₁] "⟩")] "⟩")
           "←"
           (Term.doExpr
            (Term.app
             (Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `mfirst)
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
                "=>"
                (Term.do
                 "do"
                 (Term.doSeqIndent
                  [(Term.doSeqItem
                    (Term.doLetArrow
                     "let"
                     []
                     (Term.doPatDecl
                      (Term.anonymousCtor "⟨" [`r] "⟩")
                      "←"
                      (Term.doExpr
                       (Term.app
                        `monad_lift
                        [(Term.paren
                          "("
                          [(«term_$__»
                            `Uliftable.up
                            "$"
                            (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
                           [(Term.typeAscription
                             ":"
                             (Term.app
                              `gen
                              [(«term_$__»
                                `Ulift
                                "$"
                                («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
                          ")")]))
                      []))
                    [])
                   (Term.doSeqItem
                    (Term.doExpr
                     (termIfThenElse
                      "if"
                      (Term.app `is_failure [`r])
                      "then"
                      (Term.app
                       `pure
                       [(Term.paren
                         "("
                         [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
                          [(Term.typeAscription
                            ":"
                            (Init.Data.Sigma.Basic.«termΣ_,_»
                             "Σ"
                             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                             ", "
                             («term_×_»
                              (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                              "×"
                              (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
                         ")")])
                      "else"
                      `failure))
                    [])]))))]))
           []))
         [])
        (Term.doSeqItem
         (Term.doExpr
          (termIfThenElse
           "if"
           `cfg.trace_shrink
           "then"
           («term_$__»
            `return
            "$"
            (Term.app
             `trace
             [(«term_++_»
               (termS!_
                "s!"
                (interpolatedStrKind
                 (interpolatedStrLitKind "\"{")
                 `var
                 (interpolatedStrLitKind "} := {")
                 (Term.app `reprₓ [`y])
                 (interpolatedStrLitKind "}\"")))
               "++"
               (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
              (Term.paren "(" [] ")")]))
           "else"
           (Term.app `pure [(Term.paren "(" [] ")")])))
         [])
        (Term.doSeqItem
         (Term.doExpr
          (Init.Control.Alternative.«term_<|>_»
           (Term.app `f_rec [`y `h₁ (Init.Logic.«term_+_» `n "+" (numLit "1"))])
           " <|> "
           (Term.app
            `pure
            [(Term.anonymousCtor
              "⟨"
              [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])]
              "⟩")])))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `f_rec `n] [])]
    "=>"
    (Term.do
     "do"
     (Term.doSeqIndent
      [(Term.doSeqItem
        (Term.doExpr
         (termIfThenElse
          "if"
          `cfg.trace_shrink_candidates
          "then"
          («term_$__»
           `return
           "$"
           (Term.app
            `trace
            [(termS!_
              "s!"
              (interpolatedStrKind
               (interpolatedStrLitKind "\"candidates for {")
               `var
               (interpolatedStrLitKind "} :=\n{")
               (Term.app `reprₓ [(Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `toList)])
               (interpolatedStrLitKind "}\n\"")))
             (Term.paren "(" [] ")")]))
          "else"
          (Term.app `pure [(Term.paren "(" [] ")")])))
        [])
       (Term.doSeqItem
        (Term.doLetArrow
         "let"
         []
         (Term.doPatDecl
          (Term.anonymousCtor "⟨" [`y "," `r "," (Term.anonymousCtor "⟨" [`h₁] "⟩")] "⟩")
          "←"
          (Term.doExpr
           (Term.app
            (Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `mfirst)
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
               "=>"
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doPatDecl
                     (Term.anonymousCtor "⟨" [`r] "⟩")
                     "←"
                     (Term.doExpr
                      (Term.app
                       `monad_lift
                       [(Term.paren
                         "("
                         [(«term_$__»
                           `Uliftable.up
                           "$"
                           (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
                          [(Term.typeAscription
                            ":"
                            (Term.app
                             `gen
                             [(«term_$__»
                               `Ulift
                               "$"
                               («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
                         ")")]))
                     []))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (termIfThenElse
                     "if"
                     (Term.app `is_failure [`r])
                     "then"
                     (Term.app
                      `pure
                      [(Term.paren
                        "("
                        [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
                         [(Term.typeAscription
                           ":"
                           (Init.Data.Sigma.Basic.«termΣ_,_»
                            "Σ"
                            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                            ", "
                            («term_×_»
                             (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                             "×"
                             (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
                        ")")])
                     "else"
                     `failure))
                   [])]))))]))
          []))
        [])
       (Term.doSeqItem
        (Term.doExpr
         (termIfThenElse
          "if"
          `cfg.trace_shrink
          "then"
          («term_$__»
           `return
           "$"
           (Term.app
            `trace
            [(«term_++_»
              (termS!_
               "s!"
               (interpolatedStrKind
                (interpolatedStrLitKind "\"{")
                `var
                (interpolatedStrLitKind "} := {")
                (Term.app `reprₓ [`y])
                (interpolatedStrLitKind "}\"")))
              "++"
              (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
             (Term.paren "(" [] ")")]))
          "else"
          (Term.app `pure [(Term.paren "(" [] ")")])))
        [])
       (Term.doSeqItem
        (Term.doExpr
         (Init.Control.Alternative.«term_<|>_»
          (Term.app `f_rec [`y `h₁ (Init.Logic.«term_+_» `n "+" (numLit "1"))])
          " <|> "
          (Term.app
           `pure
           [(Term.anonymousCtor
             "⟨"
             [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])]
             "⟩")])))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.do
   "do"
   (Term.doSeqIndent
    [(Term.doSeqItem
      (Term.doExpr
       (termIfThenElse
        "if"
        `cfg.trace_shrink_candidates
        "then"
        («term_$__»
         `return
         "$"
         (Term.app
          `trace
          [(termS!_
            "s!"
            (interpolatedStrKind
             (interpolatedStrLitKind "\"candidates for {")
             `var
             (interpolatedStrLitKind "} :=\n{")
             (Term.app `reprₓ [(Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `toList)])
             (interpolatedStrLitKind "}\n\"")))
           (Term.paren "(" [] ")")]))
        "else"
        (Term.app `pure [(Term.paren "(" [] ")")])))
      [])
     (Term.doSeqItem
      (Term.doLetArrow
       "let"
       []
       (Term.doPatDecl
        (Term.anonymousCtor "⟨" [`y "," `r "," (Term.anonymousCtor "⟨" [`h₁] "⟩")] "⟩")
        "←"
        (Term.doExpr
         (Term.app
          (Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `mfirst)
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
             "=>"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.anonymousCtor "⟨" [`r] "⟩")
                   "←"
                   (Term.doExpr
                    (Term.app
                     `monad_lift
                     [(Term.paren
                       "("
                       [(«term_$__»
                         `Uliftable.up
                         "$"
                         (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
                        [(Term.typeAscription
                          ":"
                          (Term.app
                           `gen
                           [(«term_$__»
                             `Ulift
                             "$"
                             («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
                       ")")]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doExpr
                  (termIfThenElse
                   "if"
                   (Term.app `is_failure [`r])
                   "then"
                   (Term.app
                    `pure
                    [(Term.paren
                      "("
                      [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
                       [(Term.typeAscription
                         ":"
                         (Init.Data.Sigma.Basic.«termΣ_,_»
                          "Σ"
                          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                          ", "
                          («term_×_»
                           (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                           "×"
                           (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
                      ")")])
                   "else"
                   `failure))
                 [])]))))]))
        []))
      [])
     (Term.doSeqItem
      (Term.doExpr
       (termIfThenElse
        "if"
        `cfg.trace_shrink
        "then"
        («term_$__»
         `return
         "$"
         (Term.app
          `trace
          [(«term_++_»
            (termS!_
             "s!"
             (interpolatedStrKind
              (interpolatedStrLitKind "\"{")
              `var
              (interpolatedStrLitKind "} := {")
              (Term.app `reprₓ [`y])
              (interpolatedStrLitKind "}\"")))
            "++"
            (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
           (Term.paren "(" [] ")")]))
        "else"
        (Term.app `pure [(Term.paren "(" [] ")")])))
      [])
     (Term.doSeqItem
      (Term.doExpr
       (Init.Control.Alternative.«term_<|>_»
        (Term.app `f_rec [`y `h₁ (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        " <|> "
        (Term.app
         `pure
         [(Term.anonymousCtor
           "⟨"
           [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])]
           "⟩")])))
      [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.do.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqIndent.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Control.Alternative.«term_<|>_»
   (Term.app `f_rec [`y `h₁ (Init.Logic.«term_+_» `n "+" (numLit "1"))])
   " <|> "
   (Term.app
    `pure
    [(Term.anonymousCtor "⟨" [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Control.Alternative.«term_<|>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `pure
   [(Term.anonymousCtor "⟨" [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`y "," (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `add_shrinks [(Init.Logic.«term_+_» `n "+" (numLit "1")) `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_shrinks
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 2, term))
  (Term.app `f_rec [`y `h₁ (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f_rec
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 3 >? 1022, (some 1023, term) <=? (some 2, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 2, (some 2, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
  (termIfThenElse
   "if"
   `cfg.trace_shrink
   "then"
   («term_$__»
    `return
    "$"
    (Term.app
     `trace
     [(«term_++_»
       (termS!_
        "s!"
        (interpolatedStrKind
         (interpolatedStrLitKind "\"{")
         `var
         (interpolatedStrLitKind "} := {")
         (Term.app `reprₓ [`y])
         (interpolatedStrLitKind "}\"")))
       "++"
       (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
      (Term.paren "(" [] ")")]))
   "else"
   (Term.app `pure [(Term.paren "(" [] ")")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pure [(Term.paren "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `return
   "$"
   (Term.app
    `trace
    [(«term_++_»
      (termS!_
       "s!"
       (interpolatedStrKind
        (interpolatedStrLitKind "\"{")
        `var
        (interpolatedStrLitKind "} := {")
        (Term.app `reprₓ [`y])
        (interpolatedStrLitKind "}\"")))
      "++"
      (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
     (Term.paren "(" [] ")")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `trace
   [(«term_++_»
     (termS!_
      "s!"
      (interpolatedStrKind
       (interpolatedStrLitKind "\"{")
       `var
       (interpolatedStrLitKind "} := {")
       (Term.app `reprₓ [`y])
       (interpolatedStrLitKind "}\"")))
     "++"
     (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
    (Term.paren "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  («term_++_»
   (termS!_
    "s!"
    (interpolatedStrKind
     (interpolatedStrLitKind "\"{")
     `var
     (interpolatedStrLitKind "} := {")
     (Term.app `reprₓ [`y])
     (interpolatedStrLitKind "}\"")))
   "++"
   (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (strLit "\"Shrink counter-example:\"")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'strLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `format_failure'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (termS!_
   "s!"
   (interpolatedStrKind
    (interpolatedStrLitKind "\"{")
    `var
    (interpolatedStrLitKind "} := {")
    (Term.app `reprₓ [`y])
    (interpolatedStrLitKind "}\"")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termS!_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `reprₓ [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `reprₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `var
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(termS!_
   "s!"
   (interpolatedStrKind
    (interpolatedStrLitKind "\"{")
    `var
    (interpolatedStrLitKind "} := {")
    (Term.app `reprₓ [`y])
    (interpolatedStrLitKind "}\"")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_++_»
   (Term.paren
    "("
    [(termS!_
      "s!"
      (interpolatedStrKind
       (interpolatedStrLitKind "\"{")
       `var
       (interpolatedStrLitKind "} := {")
       (Term.app `reprₓ [`y])
       (interpolatedStrLitKind "}\"")))
     []]
    ")")
   "++"
   (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `return
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `cfg.trace_shrink
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doLetArrow', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doLetArrow', expected 'Lean.Parser.Term.doLetArrow.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
  (Term.app
   (Term.proj (Term.app `sampleable_ext.shrink [`x]) "." `mfirst)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
      "=>"
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.anonymousCtor "⟨" [`r] "⟩")
            "←"
            (Term.doExpr
             (Term.app
              `monad_lift
              [(Term.paren
                "("
                [(«term_$__»
                  `Uliftable.up
                  "$"
                  (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
                 [(Term.typeAscription
                   ":"
                   (Term.app
                    `gen
                    [(«term_$__»
                      `Ulift
                      "$"
                      («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
                ")")]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (termIfThenElse
            "if"
            (Term.app `is_failure [`r])
            "then"
            (Term.app
             `pure
             [(Term.paren
               "("
               [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
                [(Term.typeAscription
                  ":"
                  (Init.Data.Sigma.Basic.«termΣ_,_»
                   "Σ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                   ", "
                   («term_×_»
                    (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                    "×"
                    (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
               ")")])
            "else"
            `failure))
          [])]))))])
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
    [(Term.anonymousCtor "⟨" [`a "," `h] "⟩")]
    "=>"
    (Term.do
     "do"
     (Term.doSeqIndent
      [(Term.doSeqItem
        (Term.doLetArrow
         "let"
         []
         (Term.doPatDecl
          (Term.anonymousCtor "⟨" [`r] "⟩")
          "←"
          (Term.doExpr
           (Term.app
            `monad_lift
            [(Term.paren
              "("
              [(«term_$__»
                `Uliftable.up
                "$"
                (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
               [(Term.typeAscription
                 ":"
                 (Term.app
                  `gen
                  [(«term_$__»
                    `Ulift
                    "$"
                    («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
              ")")]))
          []))
        [])
       (Term.doSeqItem
        (Term.doExpr
         (termIfThenElse
          "if"
          (Term.app `is_failure [`r])
          "then"
          (Term.app
           `pure
           [(Term.paren
             "("
             [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
              [(Term.typeAscription
                ":"
                (Init.Data.Sigma.Basic.«termΣ_,_»
                 "Σ"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                 ", "
                 («term_×_»
                  (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                  "×"
                  (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
             ")")])
          "else"
          `failure))
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.do
   "do"
   (Term.doSeqIndent
    [(Term.doSeqItem
      (Term.doLetArrow
       "let"
       []
       (Term.doPatDecl
        (Term.anonymousCtor "⟨" [`r] "⟩")
        "←"
        (Term.doExpr
         (Term.app
          `monad_lift
          [(Term.paren
            "("
            [(«term_$__»
              `Uliftable.up
              "$"
              (Term.app `testable.run [(Term.app `β [(Term.app `interp [`α `a])]) `cfg `tt]))
             [(Term.typeAscription
               ":"
               (Term.app
                `gen
                [(«term_$__»
                  `Ulift
                  "$"
                  («term_$__» `test_result "$" («term_$__» `β "$" (Term.app `interp [`α `a]))))]))]]
            ")")]))
        []))
      [])
     (Term.doSeqItem
      (Term.doExpr
       (termIfThenElse
        "if"
        (Term.app `is_failure [`r])
        "then"
        (Term.app
         `pure
         [(Term.paren
           "("
           [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
            [(Term.typeAscription
              ":"
              (Init.Data.Sigma.Basic.«termΣ_,_»
               "Σ"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
               ", "
               («term_×_»
                (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
                "×"
                (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
           ")")])
        "else"
        `failure))
      [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.do.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqIndent.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termIfThenElse
   "if"
   (Term.app `is_failure [`r])
   "then"
   (Term.app
    `pure
    [(Term.paren
      "("
      [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
       [(Term.typeAscription
         ":"
         (Init.Data.Sigma.Basic.«termΣ_,_»
          "Σ"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
          ", "
          («term_×_»
           (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
           "×"
           (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
      ")")])
   "else"
   `failure)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `failure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `pure
   [(Term.paren
     "("
     [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
      [(Term.typeAscription
        ":"
        (Init.Data.Sigma.Basic.«termΣ_,_»
         "Σ"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
         ", "
         («term_×_»
          (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
          "×"
          (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
     ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Term.anonymousCtor "⟨" [`a "," `r "," (Term.anonymousCtor "⟨" [`h] "⟩")] "⟩")
    [(Term.typeAscription
      ":"
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
       ", "
       («term_×_»
        (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
        "×"
        (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
   ", "
   («term_×_»
    (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
    "×"
    (Term.app `Plift [(Term.app `sizeof_lt [`a `x])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_×_»
   (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
   "×"
   (Term.app `Plift [(Term.app `sizeof_lt [`a `x])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Plift [(Term.app `sizeof_lt [`a `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sizeof_lt [`a `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sizeof_lt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `sizeof_lt [`a `x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Plift
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `a])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `β [(Term.app `interp [`α `a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `interp [`α `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `interp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `interp [`α `a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `β [(Term.paren "(" [(Term.app `interp [`α `a]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `test_result
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1022, (some 1023, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/--
    Shrink a counter-example `x` by using `shrink x`, picking the first
    candidate that falsifies a property and recursively shrinking that one.
    
    The process is guaranteed to terminate because `shrink x` produces
    a proof that all the values it produces are smaller (according to `sizeof`)
    than `x`. -/
  def
    minimize_aux
    [ sampleable_ext α ] [ ∀ x , testable β x ] ( cfg : slim_check_cfg ) ( var : Stringₓ )
      : proxy_repr α → ℕ → OptionTₓ gen Σ x , test_result β interp α x
    :=
      WellFounded.fix HasWellFounded.wf
        $
        fun
          x f_rec n
            =>
            do
              if
                  cfg.trace_shrink_candidates
                  then
                  return
                    $
                    trace
                      s!
                          "candidates for {
                            var
                            } :=
                            {
                            reprₓ sampleable_ext.shrink x . toList
                            }
                            "
                        ( )
                  else
                  pure ( )
                let
                  ⟨ y , r , ⟨ h₁ ⟩ ⟩
                    ←
                    sampleable_ext.shrink x . mfirst
                      fun
                        ⟨ a , h ⟩
                          =>
                          do
                            let
                                ⟨ r ⟩
                                  ←
                                  monad_lift
                                    (
                                      Uliftable.up $ testable.run β interp α a cfg tt
                                        : gen Ulift $ test_result $ β $ interp α a
                                      )
                              if
                                is_failure r
                                then
                                pure ( ⟨ a , r , ⟨ h ⟩ ⟩ : Σ a , test_result β interp α a × Plift sizeof_lt a x )
                                else
                                failure
                if
                  cfg.trace_shrink
                  then
                  return $ trace s! "{ var } := { reprₓ y }" ++ format_failure' "Shrink counter-example:" r ( )
                  else
                  pure ( )
                f_rec y h₁ n + 1 <|> pure ⟨ y , add_shrinks n + 1 r ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Once a property fails to hold on an example, look for smaller counter-examples\nto show the user. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `minimize [])
  (Command.optDeclSig
   [(Term.instBinder "[" [] (Term.app `sampleable_ext [`α]) "]")
    (Term.instBinder
     "["
     []
     (Term.forall "∀" [(Term.simpleBinder [`x] [])] "," (Term.app `testable [(Term.app `β [`x])]))
     "]")
    (Term.explicitBinder "(" [`cfg] [":" `slim_check_cfg] [] ")")
    (Term.explicitBinder "(" [`var] [":" `Stringₓ] [] ")")
    (Term.explicitBinder "(" [`x] [":" (Term.app `proxy_repr [`α])] [] ")")
    (Term.explicitBinder "(" [`r] [":" (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `x])])])] [] ")")]
   [(Term.typeSpec
     ":"
     (Term.app
      `gen
      [(Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        ", "
        (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `x])])]))]))])
  (Command.declValSimple
   ":="
   (Term.do
    "do"
    (Term.doSeqIndent
     [(Term.doSeqItem
       (Term.doExpr
        (termIfThenElse
         "if"
         `cfg.trace_shrink
         "then"
         («term_$__»
          `return
          "$"
          (Term.app
           `trace
           [(«term_++_»
             (termS!_
              "s!"
              (interpolatedStrKind
               (interpolatedStrLitKind "\"{")
               `var
               (interpolatedStrLitKind "} := {")
               (Term.app `reprₓ [`x])
               (interpolatedStrLitKind "}\"")))
             "++"
             (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
            (Term.paren "(" [] ")")]))
         "else"
         (Term.app `pure [(Term.paren "(" [] ")")])))
       [])
      (Term.doSeqItem
       (Term.doLetArrow
        "let"
        []
        (Term.doIdDecl
         `x'
         []
         "←"
         (Term.doExpr
          («term_$__» `OptionTₓ.run "$" (Term.app `minimize_aux [`α (Term.hole "_") `cfg `var `x (numLit "0")])))))
       [])
      (Term.doSeqItem
       (Term.doExpr («term_$__» `pure "$" (Term.app `x'.get_or_else [(Term.anonymousCtor "⟨" [`x "," `r] "⟩")])))
       [])]))
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
  (Term.do
   "do"
   (Term.doSeqIndent
    [(Term.doSeqItem
      (Term.doExpr
       (termIfThenElse
        "if"
        `cfg.trace_shrink
        "then"
        («term_$__»
         `return
         "$"
         (Term.app
          `trace
          [(«term_++_»
            (termS!_
             "s!"
             (interpolatedStrKind
              (interpolatedStrLitKind "\"{")
              `var
              (interpolatedStrLitKind "} := {")
              (Term.app `reprₓ [`x])
              (interpolatedStrLitKind "}\"")))
            "++"
            (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
           (Term.paren "(" [] ")")]))
        "else"
        (Term.app `pure [(Term.paren "(" [] ")")])))
      [])
     (Term.doSeqItem
      (Term.doLetArrow
       "let"
       []
       (Term.doIdDecl
        `x'
        []
        "←"
        (Term.doExpr
         («term_$__» `OptionTₓ.run "$" (Term.app `minimize_aux [`α (Term.hole "_") `cfg `var `x (numLit "0")])))))
      [])
     (Term.doSeqItem
      (Term.doExpr («term_$__» `pure "$" (Term.app `x'.get_or_else [(Term.anonymousCtor "⟨" [`x "," `r] "⟩")])))
      [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.do', expected 'Lean.Parser.Term.do.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqIndent.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» `pure "$" (Term.app `x'.get_or_else [(Term.anonymousCtor "⟨" [`x "," `r] "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `x'.get_or_else [(Term.anonymousCtor "⟨" [`x "," `r] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `r] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x'.get_or_else
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `pure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doLetArrow', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doLetArrow', expected 'Lean.Parser.Term.doLetArrow.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doIdDecl', expected 'Lean.Parser.Term.doIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
  («term_$__» `OptionTₓ.run "$" (Term.app `minimize_aux [`α (Term.hole "_") `cfg `var `x (numLit "0")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minimize_aux [`α (Term.hole "_") `cfg `var `x (numLit "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `var
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `cfg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minimize_aux
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `OptionTₓ.run
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, doElem)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqItem', expected 'Lean.Parser.Term.doSeqItem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doExpr', expected 'Lean.Parser.Term.doExpr.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
  (termIfThenElse
   "if"
   `cfg.trace_shrink
   "then"
   («term_$__»
    `return
    "$"
    (Term.app
     `trace
     [(«term_++_»
       (termS!_
        "s!"
        (interpolatedStrKind
         (interpolatedStrLitKind "\"{")
         `var
         (interpolatedStrLitKind "} := {")
         (Term.app `reprₓ [`x])
         (interpolatedStrLitKind "}\"")))
       "++"
       (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
      (Term.paren "(" [] ")")]))
   "else"
   (Term.app `pure [(Term.paren "(" [] ")")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pure [(Term.paren "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pure
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `return
   "$"
   (Term.app
    `trace
    [(«term_++_»
      (termS!_
       "s!"
       (interpolatedStrKind
        (interpolatedStrLitKind "\"{")
        `var
        (interpolatedStrLitKind "} := {")
        (Term.app `reprₓ [`x])
        (interpolatedStrLitKind "}\"")))
      "++"
      (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
     (Term.paren "(" [] ")")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `trace
   [(«term_++_»
     (termS!_
      "s!"
      (interpolatedStrKind
       (interpolatedStrLitKind "\"{")
       `var
       (interpolatedStrLitKind "} := {")
       (Term.app `reprₓ [`x])
       (interpolatedStrLitKind "}\"")))
     "++"
     (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
    (Term.paren "(" [] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  («term_++_»
   (termS!_
    "s!"
    (interpolatedStrKind
     (interpolatedStrLitKind "\"{")
     `var
     (interpolatedStrLitKind "} := {")
     (Term.app `reprₓ [`x])
     (interpolatedStrLitKind "}\"")))
   "++"
   (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (strLit "\"Shrink counter-example:\"")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'strLit', expected 'strLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `format_failure'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (termS!_
   "s!"
   (interpolatedStrKind
    (interpolatedStrLitKind "\"{")
    `var
    (interpolatedStrLitKind "} := {")
    (Term.app `reprₓ [`x])
    (interpolatedStrLitKind "}\"")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termS!_', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `reprₓ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `reprₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `var
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (some 0, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(termS!_
   "s!"
   (interpolatedStrKind
    (interpolatedStrLitKind "\"{")
    `var
    (interpolatedStrLitKind "} := {")
    (Term.app `reprₓ [`x])
    (interpolatedStrLitKind "}\"")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_++_»
   (Term.paren
    "("
    [(termS!_
      "s!"
      (interpolatedStrKind
       (interpolatedStrLitKind "\"{")
       `var
       (interpolatedStrLitKind "} := {")
       (Term.app `reprₓ [`x])
       (interpolatedStrLitKind "}\"")))
     []]
    ")")
   "++"
   (Term.app `format_failure' [(strLit "\"Shrink counter-example:\"") `r]))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trace
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `return
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `cfg.trace_shrink
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.optDeclSig', expected 'Lean.Parser.Command.optDeclSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `gen
   [(Init.Data.Sigma.Basic.«termΣ_,_»
     "Σ"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
     ", "
     (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `x])])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
   ", "
   (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `x])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `test_result [(Term.app `β [(Term.app `interp [`α `x])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `β [(Term.app `interp [`α `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `interp [`α `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `α
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `interp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `interp [`α `x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `β
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `β [(Term.paren "(" [(Term.app `interp [`α `x]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `test_result
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    Once a property fails to hold on an example, look for smaller counter-examples
    to show the user. -/
  def
    minimize
    [ sampleable_ext α ]
        [ ∀ x , testable β x ]
        ( cfg : slim_check_cfg )
        ( var : Stringₓ )
        ( x : proxy_repr α )
        ( r : test_result β interp α x )
      : gen Σ x , test_result β interp α x
    :=
      do
        if
            cfg.trace_shrink
            then
            return $ trace s! "{ var } := { reprₓ x }" ++ format_failure' "Shrink counter-example:" r ( )
            else
            pure ( )
          let x' ← OptionTₓ.run $ minimize_aux α _ cfg var x 0
          pure $ x'.get_or_else ⟨ x , r ⟩

instance (priority := 2000) exists_testable (p : Prop)
    [testable (named_binder var (∀ x, named_binder var' $ β x → p))] :
    testable (named_binder var' (named_binder var (∃ x, β x) → p)) :=
  ⟨fun cfg min => do
    let x ← testable.run (named_binder var (∀ x, named_binder var' $ β x → p)) cfg min
    pure $ convert_counter_example' exists_imp_distrib x⟩

/--  Test a universal property by creating a sample of the right type and instantiating the
bound variable with it -/
instance var_testable [sampleable_ext α] [∀ x, testable (β x)] : testable (named_binder var $ ∀ x : α, β x) :=
  ⟨fun cfg min => do
    Uliftable.adaptDown (sampleable_ext.sample α) $ fun x => do
        let r ← testable.run (β (sampleable_ext.interp α x)) cfg ff
        Uliftable.adaptDown
              (if is_failure r ∧ min then minimize _ _ cfg var x r
              else if cfg.trace_success then (trace s! "  {var } := {reprₓ x}") $ pure ⟨x, r⟩ else pure ⟨x, r⟩) $
            fun ⟨x, r⟩ =>
            return $
              trace_if_giveup cfg.trace_discarded var x r
                (add_var_to_counter_example var x (· $ sampleable_ext.interp α x) r)⟩

/--  Test a universal property about propositions -/
instance prop_var_testable (β : Prop → Prop) [I : ∀ b : Bool, testable (β b)] :
    testable (named_binder var $ ∀ p : Prop, β p) :=
  ⟨fun cfg min => do
    (convert_counter_example fun h b : Bool => h b) <$> @testable.run (named_binder var $ ∀ b : Bool, β b) _ cfg min⟩

instance (priority := 3000) unused_var_testable β [Inhabited α] [testable β] :
    testable (named_binder var $ ∀ x : α, β) :=
  ⟨fun cfg min => do
    let r ← testable.run β cfg min
    pure $ convert_counter_example (· $ default _) r (Psum.inr $ fun x _ => x)⟩

instance (priority := 2000) subtype_var_testable {p : α → Prop} [∀ x, printable_prop (p x)] [∀ x, testable (β x)]
    [I : sampleable_ext (Subtype p)] : testable (named_binder var $ ∀ x : α, named_binder var' $ p x → β x) :=
  ⟨fun cfg min => do
    let test (x : Subtype p) : testable (β x) :=
      ⟨fun cfg min => do
        let r ← testable.run (β x.val) cfg min
        match print_prop (p x) with
          | none => pure r
          | some str => pure $ add_to_counter_example (s! "guard: {str} (by construction)") id r (Psum.inr id)⟩
    let r ← @testable.run (∀ x : Subtype p, β x.val) (@SlimCheck.varTestable var _ _ I test) cfg min
    pure $ convert_counter_example' ⟨fun h : ∀ x : Subtype p, β x x h' => h ⟨x, h'⟩, fun h ⟨x, h'⟩ => h x h'⟩ r⟩

instance (priority := 100) decidable_testable (p : Prop) [printable_prop p] [Decidable p] : testable p :=
  ⟨fun cfg min =>
    return $
      if h : p then success (Psum.inr h)
      else
        match print_prop p with
        | none => failure h [] 0
        | some str => failure h [s! "issue: {str} does not hold"] 0⟩

instance eq.printable_prop {α} [HasRepr α] (x y : α) : printable_prop (x = y) :=
  ⟨some s!"{(reprₓ x)} = {reprₓ y}"⟩

instance ne.printable_prop {α} [HasRepr α] (x y : α) : printable_prop (x ≠ y) :=
  ⟨some s!"{(reprₓ x)} ≠ {reprₓ y}"⟩

instance le.printable_prop {α} [LE α] [HasRepr α] (x y : α) : printable_prop (x ≤ y) :=
  ⟨some s!"{(reprₓ x)} ≤ {reprₓ y}"⟩

instance lt.printable_prop {α} [LT α] [HasRepr α] (x y : α) : printable_prop (x < y) :=
  ⟨some s!"{(reprₓ x)} < {reprₓ y}"⟩

instance perm.printable_prop {α} [HasRepr α] (xs ys : List α) : printable_prop (xs ~ ys) :=
  ⟨some s!"{(reprₓ xs)} ~ {reprₓ ys}"⟩

instance and.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x ∧ y) :=
  ⟨do
    let x' ← print_prop x
    let y' ← print_prop y
    some s! "({x' } ∧ {y'})"⟩

instance or.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x ∨ y) :=
  ⟨do
    let x' ← print_prop x
    let y' ← print_prop y
    some s! "({x' } ∨ {y'})"⟩

instance iff.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x ↔ y) :=
  ⟨do
    let x' ← print_prop x
    let y' ← print_prop y
    some s! "({x' } ↔ {y'})"⟩

instance imp.printable_prop (x y : Prop) [printable_prop x] [printable_prop y] : printable_prop (x → y) :=
  ⟨do
    let x' ← print_prop x
    let y' ← print_prop y
    some s! "({x' } → {y'})"⟩

instance not.printable_prop (x : Prop) [printable_prop x] : printable_prop ¬x :=
  ⟨do
    let x' ← print_prop x
    some s! "¬ {x'}"⟩

instance true.printable_prop : printable_prop True :=
  ⟨some "true"⟩

instance false.printable_prop : printable_prop False :=
  ⟨some "false"⟩

instance bool.printable_prop (b : Bool) : printable_prop b :=
  ⟨some $ if b then "true" else "false"⟩

section Io

open _Root_.Nat

variable {p : Prop}

/--  Execute `cmd` and repeat every time the result is `gave_up` (at most
`n` times). -/
def retry (cmd : Rand (test_result p)) : ℕ → Rand (test_result p)
  | 0 => return $ gave_up 1
  | succ n => do
    let r ← cmd
    match r with
      | success hp => return $ success hp
      | failure Hce xs n => return (failure Hce xs n)
      | gave_up _ => retry n

/--  Count the number of times the test procedure gave up. -/
def give_up (x : ℕ) : test_result p → test_result p
  | success (Psum.inl ()) => gave_up x
  | success (Psum.inr p) => success (Psum.inr p)
  | gave_up n => gave_up (n+x)
  | failure Hce xs n => failure Hce xs n

variable (p)

variable [testable p]

/--  Try `n` times to find a counter-example for `p`. -/
def testable.run_suite_aux (cfg : slim_check_cfg) : test_result p → ℕ → Rand (test_result p)
  | r, 0 => return r
  | r, succ n => do
    let size := ((cfg.num_inst - n - 1)*cfg.max_size) / cfg.num_inst
    when cfg.trace_success $ return $ trace s!"[slim_check: sample]" ()
    let x ← retry ((testable.run p cfg tt).run ⟨size⟩) 10
    match x with
      | success (Psum.inl ()) => testable.run_suite_aux r n
      | success (Psum.inr Hp) => return $ success (Psum.inr Hp)
      | failure Hce xs n => return (failure Hce xs n)
      | gave_up g => testable.run_suite_aux (give_up g r) n

/--  Try to find a counter-example of `p`. -/
def testable.run_suite (cfg : slim_check_cfg := {  }) : Rand (test_result p) :=
  testable.run_suite_aux p cfg (success $ Psum.inl ()) cfg.num_inst

/--  Run a test suite for `p` in `io`. -/
def testable.check' (cfg : slim_check_cfg := {  }) : Io (test_result p) :=
  match cfg.random_seed with
  | some seed => Io.runRandWith seed (testable.run_suite p cfg)
  | none => Io.runRand (testable.run_suite p cfg)

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


/--  `add_existential_decorations p` adds `a `named_binder` annotation at the
root of `p` if `p` is an existential quantification. -/
unsafe def add_existential_decorations : expr → expr
  | e@(quote.1 (@Exists (%%ₓα) (%%ₓlam n bi d b))) =>
    let n := toString n
    const `` named_binder [] (quote.1 n : expr) e
  | e => e

/--  Traverse the syntax of a proposition to find universal quantifiers
and existential quantifiers and add `named_binder` annotations next to
them. -/
unsafe def add_decorations : expr → expr
  | e =>
    e.replace $ fun e _ =>
      match e with
      | pi n bi d b =>
        let n := toString n
        some $ const `` named_binder [] (quote.1 n : expr) (pi n bi (add_existential_decorations d) (add_decorations b))
      | e => none

/--  `decorations_of p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
@[reducible, nolint unused_arguments]
def decorations_of (p : Prop) :=
  Prop

/--  In a goal of the shape `⊢ tactic.decorations_of p`, `mk_decoration` examines
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
  let quote.1 (tactic.decorations_of (%%ₓp)) ← target
  exact $ add_decorations p

end Tactic

/--  Run a test suite for `p` and return true or false: should we believe that `p` holds? -/
def testable.check (p : Prop) (cfg : slim_check_cfg := {  })
    (p' : tactic.decorations_of p := by
      run_tac
        tactic.mk_decorations)
    [testable p'] : Io PUnit := do
  let x ←
    match cfg.random_seed with
      | some seed => Io.runRandWith seed (testable.run_suite p' cfg)
      | none => Io.runRand (testable.run_suite p' cfg)
  match x with
    | success _ => when ¬cfg.quiet $ Io.putStrLn "Success"
    | gave_up n => Io.fail s! "Gave up {reprₓ n} times"
    | failure _ xs n => do
      Io.fail $ format_failure "Found problems!" xs n

end Io

end SlimCheck

