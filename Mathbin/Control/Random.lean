/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Monad.Basic
import Mathbin.Data.Int.Basic
import Mathbin.Data.Stream.Defs
import Mathbin.Control.Uliftable
import Mathbin.Tactic.NormNum
import Mathbin.Data.Bitvec.Basic

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions
  * `rand` monad for computations guided by randomness;
  * `random` class for objects that can be generated randomly;
    * `random` to generate one object;
    * `random_r` to generate one object inside a range;
    * `random_series` to generate an infinite series of objects;
    * `random_series_r` to generate an infinite series of objects inside a range;
  * `io.mk_generator` to create a new random number generator;
  * `io.run_rand` to run a randomized computation inside the `io` monad;
  * `tactic.run_rand` to run a randomized computation inside the `tactic` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/


open List Io Applicativeₓ

universe u v w

/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def RandG (g : Type) (α : Type u) : Type u :=
  State (ULift.{u} g) α

/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def Rand :=
  RandG StdGen

instance (g : Type) : Uliftable (RandG.{u} g) (RandG.{v} g) :=
  @StateTₓ.uliftable' _ _ _ _ _ (Equivₓ.ulift.trans Equivₓ.ulift.symm)

open ULift hiding Inhabited

/-- Generate one more `ℕ` -/
def RandG.next {g : Type} [RandomGen g] : RandG g ℕ :=
  ⟨Prod.map id up ∘ RandomGen.next ∘ down⟩

-- mathport name: «expr .. »
local infixl:41 " .. " => Set.Icc

open Streamₓ

/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
class BoundedRandom (α : Type u) [Preorderₓ α] where
  randomR : ∀ g [RandomGen g] x y : α, x ≤ y → RandG g (x .. y)

/-- `random α` gives us machinery to generate values of type `α` -/
class Random (α : Type u) where
  Random {} : ∀ g : Type [RandomGen g], RandG g α

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift31Left : ℕ := by
  apply_normed 2 ^ 31

namespace Rand

open Streamₓ

variable (α : Type u)

variable (g : Type) [RandomGen g]

/-- create a new random number generator distinct from the one stored in the state -/
def split : RandG g g :=
  ⟨Prod.map id up ∘ RandomGen.split ∘ down⟩

variable {g}

section Random

variable [Random α]

export Random (Random)

/-- Generate a random value of type `α`. -/
def random : RandG g α :=
  Random.random α g

/-- generate an infinite series of random values of type `α` -/
def randomSeries : RandG g (Streamₓ α) := do
  let gen ← Uliftable.up (split g)
  pure <| Streamₓ.corecState (Random.random α g) gen

end Random

variable {α}

/-- Generate a random value between `x` and `y` inclusive. -/
def randomR [Preorderₓ α] [BoundedRandom α] (x y : α) (h : x ≤ y) : RandG g (x .. y) :=
  BoundedRandom.randomR g x y h

/-- generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
def randomSeriesR [Preorderₓ α] [BoundedRandom α] (x y : α) (h : x ≤ y) : RandG g (Streamₓ (x .. y)) := do
  let gen ← Uliftable.up (split g)
  pure <| corec_state (BoundedRandom.randomR g x y h) gen

end Rand

namespace Io

private def accum_char (w : ℕ) (c : Charₓ) : ℕ :=
  c.toNat + 256 * w

/-- create and a seed a random number generator -/
def mkGenerator : Io StdGen := do
  let seed ← Io.rand 0 shift31Left
  return <| mkStdGenₓ seed

variable {α : Type}

/-- Run `cmd` using a randomly seeded random number generator -/
def runRand (cmd : Rand α) : Io α := do
  let g ← Io.mkGenerator
  return <| (cmd ⟨g⟩).1

/-- Run `cmd` using the provided seed. -/
def runRandWith (seed : ℕ) (cmd : Rand α) : Io α :=
  return <| (cmd.run ⟨mkStdGenₓ seed⟩).1

section Random

variable [Random α]

/-- randomly generate a value of type α -/
def random : Io α :=
  Io.runRand (Rand.random α)

/-- randomly generate an infinite series of value of type α -/
def randomSeries : Io (Streamₓ α) :=
  Io.runRand (Rand.randomSeries α)

end Random

section BoundedRandom

variable [Preorderₓ α] [BoundedRandom α]

/-- randomly generate a value of type α between `x` and `y` -/
def randomR (x y : α) (p : x ≤ y) : Io (x .. y) :=
  Io.runRand (BoundedRandom.randomR _ x y p)

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def randomSeriesR (x y : α) (h : x ≤ y) : Io (Streamₓ <| x .. y) :=
  Io.runRand (Rand.randomSeriesR x y h)

end BoundedRandom

end Io

namespace Tactic

/-- create a seeded random number generator in the `tactic` monad -/
unsafe def mk_generator : tactic StdGen := do
  tactic.unsafe_run_io @Io.mkGenerator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
unsafe def run_rand {α : Type u} (cmd : Rand α) : tactic α := do
  let ⟨g⟩ ← tactic.up mk_generator
  return (cmd ⟨g⟩).1

variable {α : Type u}

section BoundedRandom

variable [Preorderₓ α] [BoundedRandom α]

/-- Generate a random value between `x` and `y` inclusive. -/
unsafe def random_r (x y : α) (h : x ≤ y) : tactic (x .. y) :=
  run_rand (Rand.randomR x y h)

/-- Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
unsafe def random_series_r (x y : α) (h : x ≤ y) : tactic (Streamₓ <| x .. y) :=
  run_rand (Rand.randomSeriesR x y h)

end BoundedRandom

section Random

variable [Random α]

/-- randomly generate a value of type α -/
unsafe def random : tactic α :=
  run_rand (Rand.random α)

/-- randomly generate an infinite series of value of type α -/
unsafe def random_series : tactic (Streamₓ α) :=
  run_rand (Rand.randomSeries α)

end Random

end Tactic

open Nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

variable {g : Type} [RandomGen g]

open Nat

namespace Finₓ

variable {n : ℕ} [Fact (0 < n)]

/-- generate a `fin` randomly -/
protected def random : RandG g (Finₓ n) :=
  ⟨fun ⟨g⟩ => Prod.map ofNat' up <| randNatₓ g 0 n⟩

end Finₓ

open Nat

instance natBoundedRandom : BoundedRandom ℕ where
  randomR := fun g inst x y hxy => do
    let z ← @Finₓ.random g inst (succ <| y - x) _
    pure
        ⟨z + x, Nat.le_add_leftₓ _ _, by
          rw [← le_tsub_iff_right hxy] <;> apply le_of_succ_le_succ z.is_lt⟩

/-- This `bounded_random` interval generates integers between `x` and
`y` by first generating a natural number between `0` and `y - x` and
shifting the result appropriately. -/
instance intBoundedRandom : BoundedRandom ℤ where
  randomR := fun g inst x y hxy => do
    let ⟨z, h₀, h₁⟩ ←
      @BoundedRandom.randomR ℕ _ _ g inst 0 (Int.natAbs <| y - x)
          (by
            decide)
    pure
        ⟨z + x, Int.le_add_of_nonneg_leftₓ (Int.coe_nat_nonneg _),
          Int.add_le_of_le_sub_rightₓ <|
            le_transₓ (Int.coe_nat_le_coe_nat_of_le h₁)
              (le_of_eqₓ <| Int.of_nat_nat_abs_eq_of_nonneg (Int.sub_nonneg_of_leₓ hxy))⟩

instance finRandom (n : ℕ) [Fact (0 < n)] : Random (Finₓ n) where
  Random := fun g inst => @Finₓ.random g inst _ _

instance finBoundedRandom (n : ℕ) : BoundedRandom (Finₓ n) where
  randomR := fun p => do
    let ⟨r, h, h'⟩ ← @Rand.randomR ℕ g inst _ _ x.val y.val p
    pure ⟨⟨r, lt_of_le_of_ltₓ h' y⟩, h, h'⟩

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def randomFinOfPos : ∀ {n : ℕ} h : 0 < n, Random (Finₓ n)
  | succ n, _ => finRandom _
  | 0, h => False.elim (Nat.not_lt_zeroₓ _ h)

theorem bool_of_nat_mem_Icc_of_mem_Icc_to_nat (x y : Bool) (n : ℕ) :
    n ∈ (x.toNat .. y.toNat) → Bool.ofNat n ∈ (x .. y) := by
  simp only [and_imp, Set.mem_Icc]
  intro h₀ h₁
  constructor <;> [have h₂ := Bool.of_nat_le_of_nat h₀, have h₂ := Bool.of_nat_le_of_nat h₁] <;>
    rw [Bool.of_nat_to_nat] at h₂ <;> exact h₂

instance : Random Bool where
  Random := fun g inst => (Bool.ofNat ∘ Subtype.val) <$> @BoundedRandom.randomR ℕ _ _ g inst 0 1 (Nat.zero_leₓ _)

instance : BoundedRandom Bool where
  randomR := fun g _inst x y p =>
    Subtype.map Bool.ofNat (bool_of_nat_mem_Icc_of_mem_Icc_to_nat x y) <$>
      @BoundedRandom.randomR ℕ _ _ g _inst x.toNat y.toNat (Bool.to_nat_le_to_nat p)

open_locale FinFact

/-- generate a random bit vector of length `n` -/
def Bitvec.random (n : ℕ) : RandG g (Bitvec n) :=
  Bitvec.ofFin <$> Rand.random (Finₓ <| 2 ^ n)

/-- generate a random bit vector of length `n` -/
def Bitvec.randomR {n : ℕ} (x y : Bitvec n) (h : x ≤ y) : RandG g (x .. y) :=
  have h' : ∀ a : Finₓ (2 ^ n), a ∈ (x.toFin .. y.toFin) → Bitvec.ofFin a ∈ (x .. y) := by
    simp only [and_imp, Set.mem_Icc]
    intro z h₀ h₁
    replace h₀ := Bitvec.of_fin_le_of_fin_of_le h₀
    replace h₁ := Bitvec.of_fin_le_of_fin_of_le h₁
    rw [Bitvec.of_fin_to_fin] at h₀ h₁
    constructor <;> assumption
  Subtype.map Bitvec.ofFin h' <$> Rand.randomR x.toFin y.toFin (Bitvec.to_fin_le_to_fin_of_le h)

open Nat

instance randomBitvec (n : ℕ) : Random (Bitvec n) where
  Random := fun _ inst => @Bitvec.random _ inst n

instance boundedRandomBitvec (n : ℕ) : BoundedRandom (Bitvec n) where
  randomR := fun _ inst x y p => @Bitvec.randomR _ inst _ _ _ p

