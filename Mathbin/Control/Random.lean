/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Control.Uliftable
import Data.Bitvec.Basic
import Data.Stream.Defs
import Tactic.NormNum

#align_import control.random from "leanprover-community/mathlib"@"9240e8be927a0955b9a82c6c85ef499ee3a626b8"

/-!
# Rand Monad and Random Class

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


open List Io Applicative

universe u v w

#print RandG /-
/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def RandG (g : Type) (α : Type u) : Type u :=
  StateM (ULift.{u} g) α
#align rand_g RandG
-/

#print Rand /-
/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def Rand :=
  RandG StdGen
#align rand Rand
-/

instance (g : Type) : ULiftable (RandG.{u} g) (RandG.{v} g) :=
  @StateT.uliftable' _ _ _ _ _ (Equiv.ulift.trans Equiv.ulift.symm)

open ULift hiding Inhabited

/-- Generate one more `ℕ` -/
def RandG.next {g : Type} [RandomGen g] : RandG g ℕ :=
  ⟨Prod.map id up ∘ RandomGen.next ∘ down⟩
#align rand_g.next RandG.next

local infixl:41 " .. " => Set.Icc

open Stream'

/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
class BoundedRandom (α : Type u) [Preorder α] where
  randomR : ∀ (g) [RandomGen g] (x y : α), x ≤ y → RandG g (x .. y)
#align bounded_random BoundedRandomₓ

/- ./././Mathport/Syntax/Translate/Command.lean:400:30: infer kinds are unsupported in Lean 4: #[`Randomₓ] [] -/
/-- `random α` gives us machinery to generate values of type `α` -/
class Random (α : Type u) where
  Randomₓ : ∀ (g : Type) [RandomGen g], RandG g α
#align random Randomₓ

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift31Left : ℕ := by apply_normed 2 ^ 31
#align shift_31_left shift31Left

namespace Rand

open Stream'

variable (α : Type u)

variable (g : Type) [RandomGen g]

#print Rand.split /-
/-- create a new random number generator distinct from the one stored in the state -/
def split : RandG g g :=
  ⟨Prod.map id up ∘ RandomGen.split ∘ down⟩
#align rand.split Rand.split
-/

variable {g}

section Random

variable [Random α]

export Random (Randomₓ)

/-- Generate a random value of type `α`. -/
def random : RandG g α :=
  Random.random α g
#align rand.random Rand.random

/-- generate an infinite series of random values of type `α` -/
def randomSeries : RandG g (Stream' α) := do
  let gen ← ULiftable.up (split g)
  pure <| Stream'.corecState (Random.random α g) gen
#align rand.random_series Rand.randomSeries

end Random

variable {α}

/-- Generate a random value between `x` and `y` inclusive. -/
def randomR [Preorder α] [BoundedRandom α] (x y : α) (h : x ≤ y) : RandG g (x .. y) :=
  BoundedRandom.randomR g x y h
#align rand.random_r Rand.randomR

/-- generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
def randomSeriesR [Preorder α] [BoundedRandom α] (x y : α) (h : x ≤ y) :
    RandG g (Stream' (x .. y)) := do
  let gen ← ULiftable.up (split g)
  pure <| corec_state (BoundedRandom.randomR g x y h) gen
#align rand.random_series_r Rand.randomSeriesR

end Rand

namespace Io

private def accum_char (w : ℕ) (c : Char) : ℕ :=
  c.toNat + 256 * w

/-- create and seed a random number generator -/
def mkGenerator : Io StdGen := do
  let seed ← Io.rand 0 shift31Left
  return <| mkStdGen seed
#align io.mk_generator Io.mkGenerator

variable {α : Type}

/-- Run `cmd` using a randomly seeded random number generator -/
def runRand (cmd : Rand α) : Io α := do
  let g ← Io.mkGenerator
  return <| (cmd ⟨g⟩).1
#align io.run_rand Io.runRand

/-- Run `cmd` using the provided seed. -/
def runRandWith (seed : ℕ) (cmd : Rand α) : Io α :=
  return <| (cmd.run ⟨mkStdGen seed⟩).1
#align io.run_rand_with Io.runRandWith

section Random

variable [Random α]

/-- randomly generate a value of type α -/
def random : Io α :=
  Io.runRand (Rand.random α)
#align io.random Io.random

/-- randomly generate an infinite series of value of type α -/
def randomSeries : Io (Stream' α) :=
  Io.runRand (Rand.randomSeries α)
#align io.random_series Io.randomSeries

end Random

section BoundedRandom

variable [Preorder α] [BoundedRandom α]

/-- randomly generate a value of type α between `x` and `y` -/
def randomR (x y : α) (p : x ≤ y) : Io (x .. y) :=
  Io.runRand (BoundedRandom.randomR _ x y p)
#align io.random_r Io.randomR

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def randomSeriesR (x y : α) (h : x ≤ y) : Io (Stream' <| x .. y) :=
  Io.runRand (Rand.randomSeriesR x y h)
#align io.random_series_r Io.randomSeriesR

end BoundedRandom

end Io

namespace Tactic

/-- create a seeded random number generator in the `tactic` monad -/
unsafe def mk_generator : tactic StdGen := do
  tactic.unsafe_run_io @Io.mkGenerator
#align tactic.mk_generator tactic.mk_generator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
unsafe def run_rand {α : Type u} (cmd : Rand α) : tactic α := do
  let ⟨g⟩ ← tactic.up mk_generator
  return (cmd ⟨g⟩).1
#align tactic.run_rand tactic.run_rand

variable {α : Type u}

section BoundedRandom

variable [Preorder α] [BoundedRandom α]

/-- Generate a random value between `x` and `y` inclusive. -/
unsafe def random_r (x y : α) (h : x ≤ y) : tactic (x .. y) :=
  run_rand (Rand.randomR x y h)
#align tactic.random_r tactic.random_r

/-- Generate an infinite series of random values of type `α` between `x` and `y` inclusive. -/
unsafe def random_series_r (x y : α) (h : x ≤ y) : tactic (Stream' <| x .. y) :=
  run_rand (Rand.randomSeriesR x y h)
#align tactic.random_series_r tactic.random_series_r

end BoundedRandom

section Random

variable [Random α]

/-- randomly generate a value of type α -/
unsafe def random : tactic α :=
  run_rand (Rand.random α)
#align tactic.random tactic.random

/-- randomly generate an infinite series of value of type α -/
unsafe def random_series : tactic (Stream' α) :=
  run_rand (Rand.randomSeries α)
#align tactic.random_series tactic.random_series

end Random

end Tactic

open Nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

variable {g : Type} [RandomGen g]

open Nat

namespace Fin

variable {n : ℕ} [NeZero n]

/-- generate a `fin` randomly -/
protected def random : RandG g (Fin n) :=
  ⟨fun ⟨g⟩ => Prod.map ofNat'' up <| randNat g 0 n⟩
#align fin.random Fin.random

end Fin

open Nat

instance natBoundedRandom : BoundedRandom ℕ
    where randomR g inst x y hxy := do
    let z ← @Fin.random g inst (succ <| y - x) _
    pure
        ⟨z + x, Nat.le_add_left _ _, by
          rw [← le_tsub_iff_right hxy] <;> apply le_of_succ_le_succ z.is_lt⟩
#align nat_bounded_random natBoundedRandom

/-- This `bounded_random` interval generates integers between `x` and
`y` by first generating a natural number between `0` and `y - x` and
shifting the result appropriately. -/
instance intBoundedRandom : BoundedRandom ℤ
    where randomR g inst x y hxy := do
    let ⟨z, h₀, h₁⟩ ← @BoundedRandom.randomR ℕ _ _ g inst 0 (Int.natAbs <| y - x) (by decide)
    pure
        ⟨z + x, Int.le_add_of_nonneg_left (Int.coe_nat_nonneg _),
          Int.add_le_of_le_sub_right <|
            le_trans (Int.ofNat_le_ofNat_of_le h₁)
              (le_of_eq <| Int.ofNat_natAbs_eq_of_nonneg (Int.sub_nonneg_of_le hxy))⟩
#align int_bounded_random intBoundedRandom

instance finRandom (n : ℕ) [NeZero n] : Random (Fin n)
    where Randomₓ g inst := @Fin.random g inst _ _
#align fin_random finRandom

instance finBoundedRandom (n : ℕ) : BoundedRandom (Fin n)
    where randomR g inst (x y : Fin n) p := do
    let ⟨r, h, h'⟩ ← @Rand.randomR ℕ g inst _ _ x.val y.val p
    pure ⟨⟨r, lt_of_le_of_lt h' y⟩, h, h'⟩
#align fin_bounded_random finBoundedRandom

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def randomFinOfPos : ∀ {n : ℕ} (h : 0 < n), Random (Fin n)
  | succ n, _ => finRandom _
  | 0, h => False.elim (Nat.not_lt_zero _ h)
#align random_fin_of_pos randomFinOfPos

theorem bool_ofNat_mem_Icc_of_mem_Icc_toNat (x y : Bool) (n : ℕ) :
    n ∈ (x.toNat .. y.toNat) → Bool.ofNat n ∈ (x .. y) :=
  by
  simp only [and_imp, Set.mem_Icc]; intro h₀ h₁
  constructor <;> [have h₂ := Bool.ofNat_le_ofNat h₀; have h₂ := Bool.ofNat_le_ofNat h₁] <;>
      rw [Bool.ofNat_toNat] at h₂ <;>
    exact h₂
#align bool_of_nat_mem_Icc_of_mem_Icc_to_nat bool_ofNat_mem_Icc_of_mem_Icc_toNat

instance : Random Bool
    where Randomₓ g inst :=
    (Bool.ofNat ∘ Subtype.val) <$> @BoundedRandom.randomR ℕ _ _ g inst 0 1 (Nat.zero_le _)

instance : BoundedRandom Bool
    where randomR g _inst x y p :=
    Subtype.map Bool.ofNat (bool_ofNat_mem_Icc_of_mem_Icc_toNat x y) <$>
      @BoundedRandom.randomR ℕ _ _ g _inst x.toNat y.toNat (Bool.toNat_le_toNat p)

/-- generate a random bit vector of length `n` -/
def BitVec.random (n : ℕ) : RandG g (BitVec n) :=
  BitVec.ofFin <$> Rand.random (Fin <| 2 ^ n)
#align bitvec.random BitVec.random

/-- generate a random bit vector of length `n` -/
def BitVec.randomR {n : ℕ} (x y : BitVec n) (h : x ≤ y) : RandG g (x .. y) :=
  have h' : ∀ a : Fin (2 ^ n), a ∈ (x.toFin .. y.toFin) → BitVec.ofFin a ∈ (x .. y) :=
    by
    simp only [and_imp, Set.mem_Icc]; intro z h₀ h₁
    replace h₀ := BitVec.ofFin_le_ofFin_of_le h₀
    replace h₁ := BitVec.ofFin_le_ofFin_of_le h₁
    rw [BitVec.ofFin_toFin] at h₀ h₁; constructor <;> assumption
  Subtype.map BitVec.ofFin h' <$> Rand.randomR x.toFin y.toFin (BitVec.toFin_le_toFin_of_le h)
#align bitvec.random_r BitVec.randomR

open Nat

instance randomBitvec (n : ℕ) : Random (BitVec n) where Randomₓ _ inst := @BitVec.random _ inst n
#align random_bitvec randomBitvec

instance boundedRandomBitvec (n : ℕ) : BoundedRandom (BitVec n)
    where randomR _ inst x y p := @BitVec.randomR _ inst _ _ _ p
#align bounded_random_bitvec boundedRandomBitvec

