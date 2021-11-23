import Mathbin.Data.LazyList.Basic 
import Mathbin.Data.Tree 
import Mathbin.Data.Int.Basic 
import Mathbin.Control.Bifunctor 
import Mathbin.Control.Ulift 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Testing.SlimCheck.Gen

/-!
# `sampleable` Class

This class permits the creation samples of a given type
controlling the size of those values using the `gen` monad`. It also
helps minimize examples by creating smaller versions of given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`slim_check` requires that `ℕ` have an instance of `sampleable` and for
`prime n` to be decidable.  `slim_check` will then use the instance of
`sampleable` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`slim_check` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `slim_check` moves on to trying more examples.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `sampleable` class
  * `sampleable_functor` and `sampleable_bifunctor` class
  * `sampleable_ext` class

### `sampleable`

`sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.

### `sampleable_ext`

`sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type.

### `sampleable_functor` and `sampleable_bifunctor`

`sampleable_functor F` and `sampleable_bifunctor F` makes it possible
to create samples of and shrink `F α` given a sampling function and a
shrinking function for arbitrary `α`.

This allows us to separate the logic for generating the shape of a
collection from the logic for generating its contents. Specifically,
the contents could be generated using either `sampleable` or
`sampleable_ext` instance and the `sampleable_(bi)functor` does not
need to use that information

## Shrinking

Shrinking happens when `slim_check` find a counter-example to a
property.  It is likely that the example will be more complicated than
necessary so `slim_check` proceeds to shrink it as much as
possible. Although equally valid, a smaller counter-example is easier
for a user to understand and use.

The `sampleable` class, beside having the `sample` function, has a
`shrink` function so that we can use specialized knowledge while
shrinking a value. It is not responsible for the whole shrinking process
however. It only has to take one step in the shrinking process.
`slim_check` will repeatedly call `shrink` until no more steps can
be taken. Because `shrink` guarantees that the size of the candidates
it produces is strictly smaller than the argument, we know that
`slim_check` is guaranteed to terminate.

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/


universe u v w

namespace SlimCheck

variable(α : Type u)

local infixl:50 " ≺ " => HasWellFounded.R

/-- `sizeof_lt x y` compares the sizes of `x` and `y`. -/
def sizeof_lt {α} [SizeOf α] (x y : α) :=
  sizeof x < sizeof y

/-- `shrink_fn α` is the type of functions that shrink an
argument of type `α` -/
@[reducible]
def shrink_fn (α : Type _) [SizeOf α] :=
  ∀ x : α, LazyList { y : α // sizeof_lt y x }

/-- `sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class sampleable where 
  [wf : SizeOf α]
  sample{} : gen α 
  shrink : ∀ x : α, LazyList { y : α // @sizeof _ wf y < @sizeof _ wf x } := fun _ => LazyList.nil

attribute [instance] hasWellFoundedOfHasSizeof defaultHasSizeof

attribute [instance] sampleable.wf

/-- `sampleable_functor F` makes it possible to create samples of and
shrink `F α` given a sampling function and a shrinking function for
arbitrary `α` -/
class sampleable_functor(F : Type u → Type v)[Functor F] where 
  [wf : ∀ α [SizeOf α], SizeOf (F α)]
  sample{} : ∀ {α}, gen α → gen (F α)
  shrink : ∀ α [SizeOf α], shrink_fn α → shrink_fn (F α)
  pRepr : ∀ α, HasRepr α → HasRepr (F α)

/-- `sampleable_bifunctor F` makes it possible to create samples of
and shrink `F α β` given a sampling function and a shrinking function
for arbitrary `α` and `β` -/
class sampleable_bifunctor(F : Type u → Type v → Type w)[Bifunctor F] where 
  [wf : ∀ α β [SizeOf α] [SizeOf β], SizeOf (F α β)]
  sample{} : ∀ {α β}, gen α → gen β → gen (F α β)
  shrink : ∀ α β [SizeOf α] [SizeOf β], shrink_fn α → shrink_fn β → shrink_fn (F α β)
  pRepr : ∀ α β, HasRepr α → HasRepr β → HasRepr (F α β)

export Sampleable(sample shrink)

/-- This function helps infer the proxy representation and
interpretation in `sampleable_ext` instances. -/
unsafe def sampleable.mk_trivial_interp : tactic Unit :=
  tactic.refine (pquote.1 id)

/-- `sampleable_ext` generalizes the behavior of `sampleable`
and makes it possible to express instances for types that
do not lend themselves to introspection, such as `ℕ → ℕ`.
If we test a quantification over functions the
counter-examples cannot be shrunken or printed meaningfully.

For that purpose, `sampleable_ext` provides a proxy representation
`proxy_repr` that can be printed and shrunken as well
as interpreted (using `interp`) as an object of the right type. -/
class sampleable_ext(α : Sort u) where 
  ProxyRepr : Type v
  [wf : SizeOf proxy_repr]
  interp{} : proxy_repr → α :=  by 
  runTac 
    sampleable.mk_trivial_interp
  [pRepr : HasRepr proxy_repr]
  sample{} : gen proxy_repr 
  shrink : shrink_fn proxy_repr

attribute [instance] sampleable_ext.p_repr sampleable_ext.wf

open Nat LazyList

section Prio

open SampleableExt

set_option default_priority 50

instance sampleable_ext.of_sampleable {α} [sampleable α] [HasRepr α] : sampleable_ext α :=
  { ProxyRepr := α, sample := sampleable.sample α, shrink := shrink }

instance sampleable.functor {α} {F} [Functor F] [sampleable_functor F] [sampleable α] : sampleable (F α) :=
  { wf := _, sample := sampleable_functor.sample F (sampleable.sample α),
    shrink := sampleable_functor.shrink α sampleable.shrink }

instance sampleable.bifunctor {α β} {F} [Bifunctor F] [sampleable_bifunctor F] [sampleable α] [sampleable β] :
  sampleable (F α β) :=
  { wf := _, sample := sampleable_bifunctor.sample F (sampleable.sample α) (sampleable.sample β),
    shrink := sampleable_bifunctor.shrink α β sampleable.shrink sampleable.shrink }

set_option default_priority 100

instance sampleable_ext.functor {α} {F} [Functor F] [sampleable_functor F] [sampleable_ext α] : sampleable_ext (F α) :=
  { wf := _, ProxyRepr := F (proxy_repr α), interp := Functor.map (interp _),
    sample := sampleable_functor.sample F (sampleable_ext.sample α),
    shrink := sampleable_functor.shrink _ sampleable_ext.shrink,
    pRepr := sampleable_functor.p_repr _ sampleable_ext.p_repr }

instance sampleable_ext.bifunctor {α β} {F} [Bifunctor F] [sampleable_bifunctor F] [sampleable_ext α]
  [sampleable_ext β] : sampleable_ext (F α β) :=
  { wf := _, ProxyRepr := F (proxy_repr α) (proxy_repr β), interp := Bifunctor.bimap (interp _) (interp _),
    sample := sampleable_bifunctor.sample F (sampleable_ext.sample α) (sampleable_ext.sample β),
    shrink := sampleable_bifunctor.shrink _ _ sampleable_ext.shrink sampleable_ext.shrink,
    pRepr := sampleable_bifunctor.p_repr _ _ sampleable_ext.p_repr sampleable_ext.p_repr }

end Prio

/-- `nat.shrink' k n` creates a list of smaller natural numbers by
successively dividing `n` by 2 and subtracting the difference from
`k`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink' (k : ℕ) :
  ∀ n : ℕ, n ≤ k → List { m : ℕ // HasWellFounded.R m k } → List { m : ℕ // HasWellFounded.R m k }
| n, hn, ls =>
  if h : n ≤ 1 then ls.reverse else
    have h₂ : 0 < n :=
      by 
        linarith 
    have  : (1*n) / 2 < n :=
      Nat.div_lt_of_lt_mul
        (Nat.mul_lt_mul_of_pos_rightₓ
          (by 
            normNum)
          h₂)
    have  : n / 2 < n :=
      by 
        simpa 
    let m := n / 2
    have h₀ : m ≤ k := le_transₓ (le_of_ltₓ this) hn 
    have h₃ : 0 < m :=
      by 
        simp only [m, lt_iff_add_one_le, zero_addₓ] <;> rw [Nat.le_div_iff_mul_leₓ] <;> linarith 
    have h₁ : k - m < k := Nat.sub_ltₓ (lt_of_lt_of_leₓ h₂ hn) h₃ 
    nat.shrink' m h₀ (⟨k - m, h₁⟩ :: ls)

/-- `nat.shrink n` creates a list of smaller natural numbers by
successively dividing by 2 and subtracting the difference from
`n`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink (n : ℕ) : List { m : ℕ // HasWellFounded.R m n } :=
  if h : n > 0 then
    have  : ∀ k, 1 < k → n / k < n :=
      fun k hk =>
        Nat.div_lt_of_lt_mul
          (suffices (1*n) < k*n by 
            simpa 
          Nat.mul_lt_mul_of_pos_rightₓ hk h)
    ⟨n / 11,
        this _
          (by 
            normNum)⟩ ::
      ⟨n / 3,
          this _
            (by 
              normNum)⟩ ::
        nat.shrink' n n (le_reflₓ _) []
  else []

open Gen

-- error in Testing.SlimCheck.Sampleable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
/--
Transport a `sampleable` instance from a type `α` to a type `β` using
functions between the two, going in both directions.

Function `g` is used to define the well-founded order that
`shrink` is expected to follow.
-/
def sampleable.lift
(α : Type u)
{β : Type u}
[sampleable α]
(f : α → β)
(g : β → α)
(h : ∀ a : α, «expr ≤ »(sizeof (g (f a)), sizeof a)) : sampleable β :=
{ wf := ⟨«expr ∘ »(sizeof, g)⟩,
  sample := «expr <$> »(f, sample α),
  shrink := λ
  x, have ∀
  a, «expr < »(sizeof a, sizeof (g x)) → «expr < »(sizeof (g (f a)), sizeof (g x)), by introv [ident h']; solve_by_elim [] [] ["[", expr lt_of_le_of_lt, "]"] [],
  «expr <$> »(subtype.map f this, shrink (g x)) }

instance nat.sampleable : sampleable ℕ :=
  { sample :=
      sized$
        fun sz =>
          freq [(1, coeₓ <$> choose_any (Finₓ$ succ (sz ^ 3))), (3, coeₓ <$> choose_any (Finₓ$ succ sz))]
            (by 
              decide),
    shrink := fun x => LazyList.ofList$ nat.shrink x }

/-- `iterate_shrink p x` takes a decidable predicate `p` and a
value `x` of some sampleable type and recursively shrinks `x`.
It first calls `shrink x` to get a list of candidate sample,
finds the first that satisfies `p` and recursively tries
to shrink that one. -/
def iterate_shrink {α} [HasToString α] [sampleable α] (p : α → Prop) [DecidablePred p] : α → Option α :=
  WellFounded.fix HasWellFounded.wf$
    fun x f_rec =>
      do 
        (trace s! "{x} : {(shrink x).toList}")$ pure ()
        let y ← (shrink x).find fun a => p a 
        f_rec y y.property <|> some y.val

instance fin.sampleable {n} [Fact$ 0 < n] : sampleable (Finₓ n) :=
  sampleable.lift ℕ Finₓ.ofNat' Subtype.val$ fun i => (mod_le _ _ : i % n ≤ i)

instance (priority := 100)fin.sampleable' {n} : sampleable (Finₓ (succ n)) :=
  sampleable.lift ℕ Finₓ.ofNat Subtype.val$ fun i => (mod_le _ _ : i % succ n ≤ i)

instance pnat.sampleable : sampleable ℕ+ :=
  sampleable.lift ℕ Nat.succPnat Pnat.natPred$
    fun a =>
      by 
        unfoldWf <;> simp only [Pnat.natPred, succ_pnat, Pnat.mk_coe, tsub_zero, succ_sub_succ_eq_sub]

/-- Redefine `sizeof` for `int` to make it easier to use with `nat` -/
def int.has_sizeof : SizeOf ℤ :=
  ⟨Int.natAbs⟩

attribute [local instance] int.has_sizeof

instance int.sampleable : sampleable ℤ :=
  { wf := _,
    sample :=
      sized$
        fun sz =>
          freq
            [(1,
              Subtype.val <$>
                choose (-(sz ^ 3)+1 : ℤ) ((sz ^ 3)+1)
                  (neg_le_self
                    (by 
                      decide))),
              (3,
              Subtype.val <$>
                choose (-sz+1) (sz+1)
                  (neg_le_self
                    (by 
                      decide)))]
            (by 
              decide),
    shrink :=
      fun x =>
        LazyList.ofList$
          (nat.shrink$ Int.natAbs x).bind$
            fun ⟨y, h⟩ =>
              [⟨y, h⟩,
                ⟨-y,
                  by 
                    dsimp [sizeof, SizeOf.sizeof] <;> rw [Int.nat_abs_neg] <;> exact h⟩] }

instance bool.sampleable : sampleable Bool :=
  { wf := ⟨fun b => if b then 1 else 0⟩,
    sample :=
      do 
        let x ← choose_any Bool 
        return x,
    shrink :=
      fun b =>
        if h : b then
          LazyList.singleton
            ⟨ff,
              by 
                cases h <;> unfoldWf⟩
        else LazyList.nil }

/--
Provided two shrinking functions `prod.shrink` shrinks a pair `(x, y)` by
first shrinking `x` and pairing the results with `y` and then shrinking
`y` and pairing the results with `x`.

All pairs either contain `x` untouched or `y` untouched. We rely on
shrinking being repeated for `x` to get maximally shrunken and then
for `y` to get shrunken too.
-/
def prod.shrink {α β} [SizeOf α] [SizeOf β] (shr_a : shrink_fn α) (shr_b : shrink_fn β) : shrink_fn (α × β)
| ⟨x₀, x₁⟩ =>
  let xs₀ : LazyList { y : α × β // sizeof_lt y (x₀, x₁) } :=
    (shr_a x₀).map$
      Subtype.map (fun a => (a, x₁))
        fun x h =>
          by 
            dsimp [sizeof_lt] <;> unfoldWf <;> apply h 
  let xs₁ : LazyList { y : α × β // sizeof_lt y (x₀, x₁) } :=
    (shr_b x₁).map$
      Subtype.map (fun a => (x₀, a))
        fun x h =>
          by 
            dsimp [sizeof_lt] <;> unfoldWf <;> apply h 
  xs₀.append xs₁

instance prod.sampleable : sampleable_bifunctor.{u, v} Prod :=
  { wf := _,
    sample :=
      fun α β sama samb =>
        do 
          let ⟨x⟩ ← (Uliftable.up$ sama : gen (Ulift.{max u v} α))
          let ⟨y⟩ ← (Uliftable.up$ samb : gen (Ulift.{max u v} β))
          pure (x, y),
    shrink := @prod.shrink, pRepr := @Prod.hasRepr }

instance sigma.sampleable {α β} [sampleable α] [sampleable β] : sampleable (Σ_ : α, β) :=
  (sampleable.lift (α × β) (fun ⟨x, y⟩ => ⟨x, y⟩) fun ⟨x, y⟩ => ⟨x, y⟩)$ fun ⟨x, y⟩ => le_reflₓ _

-- error in Testing.SlimCheck.Sampleable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
/-- shrinking function for sum types -/
def sum.shrink
{α β}
[has_sizeof α]
[has_sizeof β]
(shrink_α : shrink_fn α)
(shrink_β : shrink_fn β) : shrink_fn «expr ⊕ »(α, β)
| sum.inr x := «expr $ »((shrink_β x).map, «expr $ »(subtype.map sum.inr, λ
  a, by dsimp [] ["[", expr sizeof_lt, "]"] [] []; unfold_wf; solve_by_elim [] [] [] []))
| sum.inl x := «expr $ »((shrink_α x).map, «expr $ »(subtype.map sum.inl, λ
  a, by dsimp [] ["[", expr sizeof_lt, "]"] [] []; unfold_wf; solve_by_elim [] [] [] []))

instance sum.sampleable : sampleable_bifunctor.{u, v} Sum :=
  { wf := _,
    sample :=
      fun α : Type u β : Type v sam_α sam_β =>
        @Uliftable.upMap gen.{u} gen.{max u v} _ _ _ _ (@Sum.inl α β) sam_α <|>
          @Uliftable.upMap gen.{v} gen.{max v u} _ _ _ _ (@Sum.inr α β) sam_β,
    shrink := fun α β Iα Iβ shr_α shr_β => @sum.shrink _ _ Iα Iβ shr_α shr_β, pRepr := @Sum.hasRepr }

instance rat.sampleable : sampleable ℚ :=
  (sampleable.lift (ℤ × ℕ+) (fun x => Prod.casesOn x Rat.mkPnat) fun r => (r.num, ⟨r.denom, r.pos⟩))$
    by 
      intro i 
      rcases i with ⟨x, ⟨y, hy⟩⟩ <;> unfoldWf <;> dsimp [Rat.mkPnat]
      mono*
      ·
        rw [←Int.coe_nat_le, ←Int.abs_eq_nat_abs, ←Int.abs_eq_nat_abs]
        apply Int.abs_div_le_abs
      ·
        change _ - 1 ≤ y - 1
        apply tsub_le_tsub_right 
        apply Nat.div_le_of_le_mulₓ 
        suffices  : (1*y) ≤ x.nat_abs.gcd y*y
        ·
          simpa 
        apply Nat.mul_le_mul_rightₓ 
        apply gcd_pos_of_pos_right _ hy

/-- `sampleable_char` can be specialized into customized `sampleable char` instances.

The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `characters` with uniform probabilities.  -/
def sampleable_char (length : Nat) (characters : Stringₓ) : sampleable Charₓ :=
  { sample :=
      do 
        let x ←
          choose_nat 0 length
              (by 
                decide)
        if x.val = 0 then
            do 
              let n ← sample ℕ 
              pure$ Charₓ.ofNat n
          else
            do 
              let i ←
                choose_nat 0 (characters.length - 1)
                    (by 
                      decide)
              pure (characters.mk_iterator.nextn i).curr,
    shrink := fun _ => LazyList.nil }

instance char.sampleable : sampleable Charₓ :=
  sampleable_char 3 " 0123abcABC:,;`\\/"

variable{α}

section ListShrink

variable[SizeOf α](shr : ∀ x : α, LazyList { y : α // sizeof_lt y x })

-- error in Testing.SlimCheck.Sampleable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem list.sizeof_drop_lt_sizeof_of_lt_length
{xs : list α}
{k}
(hk : «expr < »(0, k))
(hk' : «expr < »(k, xs.length)) : «expr < »(sizeof (list.drop k xs), sizeof xs) :=
begin
  induction [expr xs] [] ["with", ident x, ident xs] ["generalizing", ident k],
  { cases [expr hk'] [] },
  cases [expr k] [],
  { cases [expr hk] [] },
  have [] [":", expr «expr < »(sizeof xs, sizeof [«expr :: »/«expr :: »/«expr :: »/«expr :: »](x, xs))] [],
  { unfold_wf,
    linarith [] [] [] },
  cases [expr k] [],
  { simp [] [] ["only"] ["[", expr this, ",", expr list.drop, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr list.drop, "]"] [] [],
    transitivity [],
    { solve_by_elim [] [] ["[", expr xs_ih, ",", expr lt_of_succ_lt_succ hk', ",", expr zero_lt_succ, "]"] [] },
    { assumption } }
end

theorem list.sizeof_cons_lt_right (a b : α) {xs : List α} (h : sizeof a < sizeof b) :
  sizeof (a :: xs) < sizeof (b :: xs) :=
  by 
    unfoldWf <;> assumption

theorem list.sizeof_cons_lt_left (x : α) {xs xs' : List α} (h : sizeof xs < sizeof xs') :
  sizeof (x :: xs) < sizeof (x :: xs') :=
  by 
    unfoldWf <;> assumption

theorem list.sizeof_append_lt_left {xs ys ys' : List α} (h : sizeof ys < sizeof ys') :
  sizeof (xs ++ ys) < sizeof (xs ++ ys') :=
  by 
    induction xs
    ·
      apply h
    ·
      unfoldWf 
      simp only [List.sizeof, add_lt_add_iff_left]
      exact xs_ih

theorem list.one_le_sizeof (xs : List α) : 1 ≤ sizeof xs :=
  by 
    cases xs <;> unfoldWf <;> linarith

-- error in Testing.SlimCheck.Sampleable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
/--
`list.shrink_removes` shrinks a list by removing chunks of size `k` in
the middle of the list.
-/
def list.shrink_removes
(k : exprℕ())
(hk : «expr < »(0, k)) : ∀ (xs : list α) (n), «expr = »(n, xs.length) → lazy_list {ys : list α // sizeof_lt ys xs}
| xs, n, hn := if hkn : «expr > »(k, n) then lazy_list.nil else if hkn' : «expr = »(k, n) then have «expr < »(1, xs.sizeof), by { subst_vars,
  cases [expr xs] [],
  { contradiction },
  unfold_wf,
  apply [expr lt_of_lt_of_le],
  show [expr «expr < »(1, «expr + »(«expr + »(1, has_sizeof.sizeof xs_hd), 1))],
  { linarith [] [] [] },
  { mono [] [] [] [],
    apply [expr list.one_le_sizeof] } },
lazy_list.singleton ⟨«expr[ , ]»([]), this⟩ else have h₂ : «expr < »(k, xs.length), from «expr ▸ »(hn, lt_of_le_of_ne (le_of_not_gt hkn) hkn'),
match list.split_at k xs, rfl : ∀ ys, «expr = »(ys, list.split_at k xs) → _ with
| ⟨xs₁, xs₂⟩, h := have h₄ : «expr = »(xs₁, xs.take k), by simp [] [] ["only"] ["[", expr list.split_at_eq_take_drop, ",", expr prod.mk.inj_iff, "]"] [] ["at", ident h]; tauto [],
have h₃ : «expr = »(xs₂, xs.drop k), by simp [] [] ["only"] ["[", expr list.split_at_eq_take_drop, ",", expr prod.mk.inj_iff, "]"] [] ["at", ident h]; tauto [],
have «expr < »(sizeof xs₂, sizeof xs), by rw [expr h₃] []; solve_by_elim [] [] ["[", expr list.sizeof_drop_lt_sizeof_of_lt_length, "]"] [],
have h₁ : «expr = »(«expr - »(n, k), xs₂.length), by simp [] [] ["only"] ["[", expr h₃, ",", "<-", expr hn, ",", expr list.length_drop, "]"] [] [],
have h₅ : ∀
a : list α, sizeof_lt a xs₂ → sizeof_lt «expr ++ »(xs₁, a) xs, by intros [ident a, ident h]; rw ["[", "<-", expr list.take_append_drop k xs, ",", "<-", expr h₃, ",", "<-", expr h₄, "]"] []; solve_by_elim [] [] ["[", expr list.sizeof_append_lt_left, "]"] [],
«expr $ »(lazy_list.cons ⟨xs₂, this⟩, «expr <$> »(subtype.map (((«expr ++ »)) xs₁) h₅, list.shrink_removes xs₂ «expr - »(n, k) h₁))
end

/--
`list.shrink_one xs` shrinks list `xs` by shrinking only one item in
the list.
-/
def list.shrink_one : shrink_fn (List α)
| [] => LazyList.nil
| x :: xs =>
  LazyList.append ((Subtype.map (fun x' => x' :: xs) fun a => list.sizeof_cons_lt_right _ _) <$> shr x)
    ((Subtype.map ((· :: ·) x) fun _ => list.sizeof_cons_lt_left _) <$> list.shrink_one xs)

/-- `list.shrink_with shrink_f xs` shrinks `xs` by first
considering `xs` with chunks removed in the middle (starting with
chunks of size `xs.length` and halving down to `1`) and then
shrinks only one element of the list.

This strategy is taken directly from Haskell's QuickCheck -/
def list.shrink_with (xs : List α) : LazyList { ys : List α // sizeof_lt ys xs } :=
  let n := xs.length 
  LazyList.append
    ((LazyList.cons n$ (shrink n).reverse.map Subtype.val).bind
      fun k => if hk : 0 < k then list.shrink_removes k hk xs n rfl else LazyList.nil)
    (list.shrink_one shr _)

end ListShrink

instance list.sampleable : sampleable_functor List.{u} :=
  { wf := _, sample := fun α sam_α => list_of sam_α, shrink := fun α Iα shr_α => @list.shrink_with _ Iα shr_α,
    pRepr := @List.hasRepr }

instance Prop.sampleable_ext : sampleable_ext Prop :=
  { ProxyRepr := Bool, interp := coeₓ, sample := choose_any Bool, shrink := fun _ => LazyList.nil }

/-- `no_shrink` is a type annotation to signal that
a certain type is not to be shrunk. It can be useful in
combination with other types: e.g. `xs : list (no_shrink ℤ)`
will result in the list being cut down but individual
integers being kept as is. -/
def no_shrink (α : Type _) :=
  α

instance no_shrink.inhabited {α} [Inhabited α] : Inhabited (no_shrink α) :=
  ⟨(default α : α)⟩

/-- Introduction of the `no_shrink` type. -/
def no_shrink.mk {α} (x : α) : no_shrink α :=
  x

/-- Selector of the `no_shrink` type. -/
def no_shrink.get {α} (x : no_shrink α) : α :=
  x

instance no_shrink.sampleable {α} [sampleable α] : sampleable (no_shrink α) :=
  { sample := no_shrink.mk <$> sample α }

instance string.sampleable : sampleable Stringₓ :=
  { sampleable.lift (List Charₓ) List.asStringₓ Stringₓ.toList$ fun _ => le_reflₓ _ with
    sample :=
      do 
        let x ← list_of (sample Charₓ)
        pure x.as_string }

/-- implementation of `sampleable (tree α)` -/
def tree.sample (sample : gen α) : ℕ → gen (Tree α)
| n =>
  if h : n > 0 then
    have  : n / 2 < n :=
      div_lt_self h
        (by 
          normNum)
    ((Tree.node <$> sample)<*>tree.sample (n / 2))<*>tree.sample (n / 2)
  else pure Tree.nil

/-- `rec_shrink x f_rec` takes the recursive call `f_rec` introduced
by `well_founded.fix` and turns it into a shrinking function whose
result is adequate to use in a recursive call. -/
def rec_shrink {α : Type _} [SizeOf α] (t : α) (sh : ∀ x : α, sizeof_lt x t → LazyList { y : α // sizeof_lt y x }) :
  shrink_fn { t' : α // sizeof_lt t' t }
| ⟨t', ht'⟩ =>
  (fun t'' : { y : α // sizeof_lt y t' } => ⟨⟨t''.val, lt_transₓ t''.property ht'⟩, t''.property⟩) <$> sh t' ht'

theorem tree.one_le_sizeof {α} [SizeOf α] (t : Tree α) : 1 ≤ sizeof t :=
  by 
    cases t <;> unfoldWf <;> linarith

instance  : Functor Tree :=
  { map := @Tree.mapₓ }

/--
Recursion principle for shrinking tree-like structures.
-/
def rec_shrink_with [SizeOf α]
  (shrink_a : ∀ x : α, shrink_fn { y : α // sizeof_lt y x } → List (LazyList { y : α // sizeof_lt y x })) :
  shrink_fn α :=
  WellFounded.fix (sizeof_measure_wf _)$
    fun t f_rec => LazyList.join (LazyList.ofList$ shrink_a t$ fun ⟨t', h⟩ => rec_shrink _ f_rec _)

theorem rec_shrink_with_eq [SizeOf α]
  (shrink_a : ∀ x : α, shrink_fn { y : α // sizeof_lt y x } → List (LazyList { y : α // sizeof_lt y x })) (x : α) :
  rec_shrink_with shrink_a x =
    LazyList.join (LazyList.ofList$ shrink_a x$ fun t' => rec_shrink _ (fun x h' => rec_shrink_with shrink_a x) _) :=
  by 
    convLHS => rw [rec_shrink_with, WellFounded.fix_eq]
    congr 
    ext ⟨y, h⟩
    rfl

-- error in Testing.SlimCheck.Sampleable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `tree.shrink_with shrink_f t` shrinks `xs` by using the empty tree,
each subtrees, and by shrinking the subtree to recombine them.

This strategy is taken directly from Haskell's QuickCheck -/
def tree.shrink_with [has_sizeof α] (shrink_a : shrink_fn α) : shrink_fn (tree α) :=
«expr $ »(rec_shrink_with, λ t, match t with
 | tree.nil := λ f_rec, «expr[ , ]»([])
 | tree.node x t₀ t₁ := λ
 f_rec, have h₂ : sizeof_lt tree.nil (tree.node x t₀ t₁), by clear [ident _match]; have [] [] [":=", expr tree.one_le_sizeof t₀]; dsimp [] ["[", expr sizeof_lt, ",", expr sizeof, ",", expr has_sizeof.sizeof, "]"] [] ["at", "*"]; unfold_wf; linarith [] [] [],
 have h₀ : sizeof_lt t₀ (tree.node x t₀ t₁), by dsimp [] ["[", expr sizeof_lt, "]"] [] []; unfold_wf; linarith [] [] [],
 have h₁ : sizeof_lt t₁ (tree.node x t₀ t₁), by dsimp [] ["[", expr sizeof_lt, "]"] [] []; unfold_wf; linarith [] [] [],
 «expr[ , ]»([lazy_list.of_list «expr[ , ]»([⟨tree.nil, h₂⟩, ⟨t₀, h₀⟩, ⟨t₁, h₁⟩]), «expr $ »((prod.shrink shrink_a (prod.shrink f_rec f_rec) (x, ⟨t₀, h₀⟩, ⟨t₁, h₁⟩)).map, λ
    ⟨⟨y, ⟨t'₀, _⟩, ⟨t'₁, _⟩⟩, hy⟩, ⟨tree.node y t'₀ t'₁, by revert [ident hy]; dsimp [] ["[", expr sizeof_lt, "]"] [] []; unfold_wf; intro []; linarith [] [] []⟩)])
 end)

instance sampleable_tree : sampleable_functor Tree :=
  { wf := _, sample := fun α sam_α => sized$ tree.sample sam_α,
    shrink := fun α Iα shr_α => @tree.shrink_with _ Iα shr_α, pRepr := @Tree.hasRepr }

/-- Type tag that signals to `slim_check` to use small values for a given type. -/
def small (α : Type _) :=
  α

/-- Add the `small` type tag -/
def small.mk {α} (x : α) : small α :=
  x

/-- Type tag that signals to `slim_check` to use large values for a given type. -/
def large (α : Type _) :=
  α

/-- Add the `large` type tag -/
def large.mk {α} (x : α) : large α :=
  x

instance small.functor : Functor small :=
  id.monad.toFunctor

instance large.functor : Functor large :=
  id.monad.toFunctor

instance small.inhabited [Inhabited α] : Inhabited (small α) :=
  ⟨(default α : α)⟩

instance large.inhabited [Inhabited α] : Inhabited (large α) :=
  ⟨(default α : α)⟩

instance small.sampleable_functor : sampleable_functor small :=
  { wf := _, sample := fun α samp => gen.resize (fun n => (n / 5)+5) samp, shrink := fun α _ => id,
    pRepr := fun α => id }

instance large.sampleable_functor : sampleable_functor large :=
  { wf := _, sample := fun α samp => gen.resize (fun n => n*5) samp, shrink := fun α _ => id, pRepr := fun α => id }

instance ulift.sampleable_functor : sampleable_functor Ulift.{u, v} :=
  { wf := fun α h => ⟨fun ⟨x⟩ => @sizeof α h x⟩, sample := fun α samp => Uliftable.upMap Ulift.up$ samp,
    shrink := fun α _ shr ⟨x⟩ => (shr x).map (Subtype.map Ulift.up fun a h => h),
    pRepr := fun α h => ⟨@reprₓ α h ∘ Ulift.down⟩ }

/-!
## Subtype instances

The following instances are meant to improve the testing of properties of the form
`∀ i j, i ≤ j, ...`

The naive way to test them is to choose two numbers `i` and `j` and check that
the proper ordering is satisfied. Instead, the following instances make it
so that `j` will be chosen with considerations to the required ordering
constraints. The benefit is that we will not have to discard any choice
of `j`.
 -/


/-! ### Subtypes of `ℕ` -/


instance nat_le.sampleable {y} : SlimCheck.Sampleable { x : ℕ // x ≤ y } :=
  { sample :=
      do 
        let ⟨x, h⟩ ←
          SlimCheck.Gen.chooseNat 0 y
              (by 
                decide)
        pure ⟨x, h.2⟩,
    shrink :=
      fun ⟨x, h⟩ =>
        (fun a : Subtype _ => Subtype.recOn a$ fun x' h' => ⟨⟨x', le_transₓ (le_of_ltₓ h') h⟩, h'⟩) <$> shrink x }

instance nat_ge.sampleable {x} : SlimCheck.Sampleable { y : ℕ // x ≤ y } :=
  { sample :=
      do 
        let (y : ℕ) ← SlimCheck.Sampleable.sample ℕ 
        pure
            ⟨x+y,
              by 
                normNum⟩,
    shrink :=
      fun ⟨y, h⟩ =>
        (fun a : { y' // sizeof y' < sizeof (y - x) } =>
            Subtype.recOn a$ fun δ h' => ⟨⟨x+δ, Nat.le_add_rightₓ _ _⟩, lt_tsub_iff_left.mp h'⟩) <$>
          shrink (y - x) }

instance nat_gt.sampleable {x} : SlimCheck.Sampleable { y : ℕ // x < y } :=
  { sample :=
      do 
        let (y : ℕ) ← SlimCheck.Sampleable.sample ℕ 
        pure
            ⟨(x+y)+1,
              by 
                linarith⟩,
    shrink := fun x => shrink _ }

/-! ### Subtypes of any `linear_ordered_add_comm_group` -/


instance le.sampleable {y : α} [sampleable α] [LinearOrderedAddCommGroup α] : SlimCheck.Sampleable { x : α // x ≤ y } :=
  { sample :=
      do 
        let x ← sample α 
        pure ⟨y - |x|, sub_le_self _ (abs_nonneg _)⟩,
    shrink := fun _ => LazyList.nil }

instance ge.sampleable {x : α} [sampleable α] [LinearOrderedAddCommGroup α] : SlimCheck.Sampleable { y : α // x ≤ y } :=
  { sample :=
      do 
        let y ← sample α 
        pure
            ⟨x+|y|,
              by 
                normNum [abs_nonneg]⟩,
    shrink := fun _ => LazyList.nil }

/-!
### Subtypes of `ℤ`

Specializations of `le.sampleable` and `ge.sampleable` for `ℤ` to help instance search.
-/


instance int_le.sampleable {y : ℤ} : SlimCheck.Sampleable { x : ℤ // x ≤ y } :=
  sampleable.lift ℕ
    (fun n =>
      ⟨y - n,
        Int.sub_left_le_of_le_add$
          by 
            simp ⟩)
    (fun ⟨i, h⟩ => (y - i).natAbs)
    fun n =>
      by 
        unfoldWf <;> simp [int_le.sampleable._match_1] <;> ring

instance int_ge.sampleable {x : ℤ} : SlimCheck.Sampleable { y : ℤ // x ≤ y } :=
  sampleable.lift ℕ
    (fun n =>
      ⟨x+n,
        by 
          simp ⟩)
    (fun ⟨i, h⟩ => (i - x).natAbs)
    fun n =>
      by 
        unfoldWf <;> simp [int_ge.sampleable._match_1] <;> ring

instance int_lt.sampleable {y} : SlimCheck.Sampleable { x : ℤ // x < y } :=
  sampleable.lift ℕ
    (fun n =>
      ⟨y - n+1,
        Int.sub_left_lt_of_lt_add$
          by 
            linarith [Int.coe_nat_nonneg n]⟩)
    (fun ⟨i, h⟩ => (y - i - 1).natAbs)
    fun n =>
      by 
        unfoldWf <;> simp [int_lt.sampleable._match_1] <;> ring

instance int_gt.sampleable {x} : SlimCheck.Sampleable { y : ℤ // x < y } :=
  sampleable.lift ℕ
    (fun n =>
      ⟨x+n+1,
        by 
          linarith⟩)
    (fun ⟨i, h⟩ => (i - x - 1).natAbs)
    fun n =>
      by 
        unfoldWf <;> simp [int_gt.sampleable._match_1] <;> ring

/-! ### Subtypes of any `list` -/


instance perm.slim_check {xs : List α} : SlimCheck.Sampleable { ys : List α // List.Perm xs ys } :=
  { sample := permutation_of xs, shrink := fun _ => LazyList.nil }

instance perm'.slim_check {xs : List α} : SlimCheck.Sampleable { ys : List α // List.Perm ys xs } :=
  { sample := Subtype.map id (@List.Perm.symm α _) <$> permutation_of xs, shrink := fun _ => LazyList.nil }

setup_tactic_parser

open Tactic

/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def print_samples {t : Type u} [HasRepr t] (g : gen t) : Io Unit :=
  do 
    let xs ←
      Io.runRand$
          Uliftable.down$
            do 
              let xs ← (List.range 10).mmap$ g.run ∘ Ulift.up 
              pure ⟨xs.map reprₓ⟩
    xs.mmap' Io.putStrLn

/-- Create a `gen α` expression from the argument of `#sample` -/
unsafe def mk_generator (e : expr) : tactic (expr × expr) :=
  do 
    let t ← infer_type e 
    match t with 
      | quote.1 (gen (%%ₓt)) =>
        do 
          let repr_inst ← mk_app `` HasRepr [t] >>= mk_instance 
          pure (repr_inst, e)
      | _ =>
        do 
          let samp_inst ← to_expr (pquote.1 (sampleable_ext (%%ₓe))) >>= mk_instance 
          let repr_inst ← mk_mapp `` sampleable_ext.p_repr [e, samp_inst]
          let gen ← mk_mapp `` sampleable_ext.sample [none, samp_inst]
          pure (repr_inst, gen)

/--
`#sample my_type`, where `my_type` has an instance of `sampleable`, prints ten random
values of type `my_type` of using an increasing size parameter.

```lean
#sample nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample list int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
@[user_command]
unsafe def sample_cmd (_ : parse$ tk "#sample") : lean.parser Unit :=
  do 
    let e ← texpr 
    of_tactic$
        do 
          let e ← i_to_expr e 
          let (repr_inst, gen) ← mk_generator e 
          let print_samples ← mk_mapp `` print_samples [none, repr_inst, gen]
          let sample ← eval_expr (Io Unit) print_samples 
          unsafe_run_io sample

end SlimCheck

