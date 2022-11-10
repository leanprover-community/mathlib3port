/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.Algebra.GcdMonoid.Finset
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.RingTheory.Int.Basic
import Mathbin.RingTheory.Polynomial.Content

/-!
# Basic results about setwise gcds on normalized gcd monoid with a division.

## Main results

* `finset.nat.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from `s` to
  `ℕ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `finset.int.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from `s` to
  `ℤ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `finset.polynomial.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from
  `s` to `K[X]`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.

## TODO
Add a typeclass to state these results uniformly.

-/


namespace Finset

namespace Nat

/-- Given a nonempty finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type _} {f : β → ℕ} (s : Finset β) {x : β} (hx : x ∈ s) (hfz : f x ≠ 0) :
    (s.gcd fun b => f b / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' ((Finset.gcd_congr rfl) fun a ha => _).trans hg
  rw [he a ha, Nat.mul_div_cancel_left]
  exact Nat.pos_of_ne_zero (mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx)

theorem gcd_div_id_eq_one {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) (hnz : x ≠ 0) : (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz

end Nat

namespace Int

/-- Given a nonempty finset `s` and a function `f` from `s` to `ℤ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type _} {f : β → ℤ} (s : Finset β) {x : β} (hx : x ∈ s) (hfz : f x ≠ 0) :
    (s.gcd fun b => f b / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' ((Finset.gcd_congr rfl) fun a ha => _).trans hg
  rw [he a ha, Int.mul_div_cancel_left]
  exact mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx

theorem gcd_div_id_eq_one {s : Finset ℤ} {x : ℤ} (hx : x ∈ s) (hnz : x ≠ 0) : (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz

end Int

namespace Polynomial

open Polynomial Classical

noncomputable section

variable {K : Type _} [Field K]

/-- Given a nonempty finset `s` and a function `f` from `s` to `K[X]`, if `d = s.gcd f`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type _} {f : β → K[X]} (s : Finset β) {x : β} (hx : x ∈ s) (hfz : f x ≠ 0) :
    (s.gcd fun b => f b / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' ((Finset.gcd_congr rfl) fun a ha => _).trans hg
  rw [he a ha, EuclideanDomain.mul_div_cancel_left]
  exact mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx

theorem gcd_div_id_eq_one {s : Finset K[X]} {x : K[X]} (hx : x ∈ s) (hnz : x ≠ 0) : (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz

end Polynomial

end Finset

