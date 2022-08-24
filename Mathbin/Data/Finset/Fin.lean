/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Scott Morrison, Johan Commelin
-/
import Mathbin.Data.Finset.Card

/-!
# Finsets in `fin n`

A few constructions for finsets in `fin n`.

## Main declarations

* `finset.attach_fin`: Turns a finset of naturals strictly less than `n` into a `finset (fin n)`.
-/


variable {n : ℕ}

namespace Finset

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attachFin (s : Finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : Finset (Finₓ n) :=
  ⟨s.1.pmap (fun a ha => ⟨a, ha⟩) h, s.Nodup.pmap fun _ _ _ _ => Finₓ.veq_of_eq⟩

@[simp]
theorem mem_attach_fin {n : ℕ} {s : Finset ℕ} (h : ∀ m ∈ s, m < n) {a : Finₓ n} : a ∈ s.attachFin h ↔ (a : ℕ) ∈ s :=
  ⟨fun h =>
    let ⟨b, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h => Multiset.mem_pmap.2 ⟨a, h, Finₓ.eta _ _⟩⟩

@[simp]
theorem card_attach_fin {n : ℕ} (s : Finset ℕ) (h : ∀ m ∈ s, m < n) : (s.attachFin h).card = s.card :=
  Multiset.card_pmap _ _ _

end Finset

