import Mathbin.Control.Random 
import Mathbin.Control.Uliftable

/-!
# `gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `gen` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/


universe u v

namespace SlimCheck

-- error in Testing.SlimCheck.Gen: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler monad
/-- Monad to generate random examples to test properties with.
It has a `nat` parameter so that the caller can decide on the
size of the examples. -/ @[reducible, derive #["[", expr monad, ",", expr is_lawful_monad, "]"]] def gen (α : Type u) :=
reader_t (ulift exprℕ()) rand α

variable(α : Type u)

local infixl:41 " .. " => Set.Icc

/-- Execute a `gen` inside the `io` monad using `i` as the example
size and with a fresh random number generator. -/
def io.run_gen {α} (x : gen α) (i : ℕ) : Io α :=
  Io.runRand (x.run ⟨i⟩)

namespace Gen

section Rand

/-- Lift `random.random` to the `gen` monad. -/
def choose_any [Random α] : gen α :=
  ⟨fun _ => Rand.random α⟩

variable{α}[Preorderₓ α]

/-- Lift `random.random_r` to the `gen` monad. -/
def choose [BoundedRandom α] (x y : α) (p : x ≤ y) : gen (x .. y) :=
  ⟨fun _ => Rand.randomR x y p⟩

end Rand

open Nat hiding choose

/-- Generate a `nat` example between `x` and `y`. -/
def choose_nat (x y : ℕ) (p : x ≤ y) : gen (x .. y) :=
  choose x y p

-- error in Testing.SlimCheck.Gen: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Generate a `nat` example between `x` and `y`. -/
def choose_nat' (x y : exprℕ()) (p : «expr < »(x, y)) : gen (set.Ico x y) :=
have ∀
i, «expr < »(x, i) → «expr ≤ »(i, y) → «expr < »(i.pred, y), from λ
i
h₀
h₁, show «expr ≤ »(i.pred.succ, y), by rwa [expr succ_pred_eq_of_pos] []; apply [expr lt_of_le_of_lt (nat.zero_le _) h₀],
«expr <$> »(subtype.map pred (λ
  (i)
  (h : «expr ∧ »(«expr ≤ »(«expr + »(x, 1), i), «expr ≤ »(i, y))), ⟨le_pred_of_lt h.1, this _ h.1 h.2⟩), choose «expr + »(x, 1) y p)

open Nat

instance  : Uliftable gen.{u} gen.{v} :=
  ReaderTₓ.uliftable' (Equiv.ulift.trans Equiv.ulift.symm)

instance  : HasOrelse gen.{u} :=
  ⟨fun α x y =>
      do 
        let b ← Uliftable.up$ choose_any Bool 
        if b.down then x else y⟩

variable{α}

/-- Get access to the size parameter of the `gen` monad. For
reasons of universe polymorphism, it is specified in
continuation passing style. -/
def sized (cmd : ℕ → gen α) : gen α :=
  ⟨fun ⟨sz⟩ => ReaderTₓ.run (cmd sz) ⟨sz⟩⟩

/-- Apply a function to the size parameter. -/
def resize (f : ℕ → ℕ) (cmd : gen α) : gen α :=
  ⟨fun ⟨sz⟩ => ReaderTₓ.run cmd ⟨f sz⟩⟩

/-- Create `n` examples using `cmd`. -/
def vector_of : ∀ (n : ℕ) (cmd : gen α), gen (Vector α n)
| 0, _ => return Vector.nil
| succ n, cmd => (Vector.cons <$> cmd)<*>vector_of n cmd

/-- Create a list of examples using `cmd`. The size is controlled
by the size parameter of `gen`. -/
def list_of (cmd : gen α) : gen (List α) :=
  sized$
    fun sz =>
      do 
        do 
            let ⟨n⟩ ←
              Uliftable.up$
                  choose_nat 0 (sz+1)
                    (by 
                      decide)
            let v ← vector_of n.val cmd 
            return v.to_list

open Ulift

/-- Given a list of example generators, choose one to create an example. -/
def one_of (xs : List (gen α)) (pos : 0 < xs.length) : gen α :=
  do 
    let ⟨⟨n, h, h'⟩⟩ ← Uliftable.up$ choose_nat' 0 xs.length Pos 
    List.nthLe xs n h'

/-- Given a list of example generators, choose one to create an example. -/
def elements (xs : List α) (pos : 0 < xs.length) : gen α :=
  do 
    let ⟨⟨n, h₀, h₁⟩⟩ ← Uliftable.up$ choose_nat' 0 xs.length Pos 
    pure$ List.nthLe xs n h₁

/--
`freq_aux xs i _` takes a weighted list of generator and a number meant to select one of the
generators.

If we consider `freq_aux [(1, gena), (3, genb), (5, genc)] 4 _`, we choose a generator by splitting
the interval 1-9 into 1-1, 2-4, 5-9 so that the width of each interval corresponds to one of the
number in the list of generators. Then, we check which interval 4 falls into: it selects `genb`.
-/
def freq_aux : ∀ (xs : List (ℕ+ × gen α)) i, i < (xs.map (Subtype.val ∘ Prod.fst)).Sum → gen α
| [], i, h => False.elim (Nat.not_lt_zeroₓ _ h)
| (i, x) :: xs, j, h =>
  if h' : j < i then x else
    freq_aux xs (j - i)
      (by 
        rw [tsub_lt_iff_right (le_of_not_gtₓ h')]
        simpa [List.sum_cons, add_commₓ] using h)

/--
`freq [(1, gena), (3, genb), (5, genc)] _` will choose one of `gena`, `genb`, `genc` with
probabilities proportional to the number accompanying them. In this example, the sum of
those numbers is 9, `gena` will be chosen with probability ~1/9, `genb` with ~3/9 (i.e. 1/3)
and `genc` with probability 5/9.
-/
def freq (xs : List (ℕ+ × gen α)) (pos : 0 < xs.length) : gen α :=
  let s := (xs.map (Subtype.val ∘ Prod.fst)).Sum 
  have ha : 1 ≤ s :=
    le_transₓ Pos$
      List.length_map (Subtype.val ∘ Prod.fst) xs ▸
        List.length_le_sum_of_one_le _
          fun i =>
            by 
              simp 
              intros 
              assumption 
  have  : 0 ≤ s - 1 := le_tsub_of_add_le_right ha 
  Uliftable.adaptUp gen.{0} gen.{u} (choose_nat 0 (s - 1) this)$
    fun i =>
      freq_aux xs i.1
        (by 
          rcases i with ⟨i, h₀, h₁⟩ <;> rwa [le_tsub_iff_right] at h₁ <;> exact ha)

/-- Generate a random permutation of a given list. -/
def permutation_of {α : Type u} : ∀ (xs : List α), gen (Subtype$ List.Perm xs)
| [] => pure ⟨[], List.Perm.nil⟩
| x :: xs =>
  do 
    let ⟨xs', h⟩ ← permutation_of xs 
    let ⟨⟨n, _, h'⟩⟩ ←
      Uliftable.up$
          choose_nat 0 xs'.length
            (by 
              decide)
    pure ⟨List.insertNth n x xs', List.Perm.trans (List.Perm.cons _ h) (List.perm_insert_nth _ _ h').symm⟩

end Gen

end SlimCheck

