/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Data.DFinsupp.Lex
import Order.GameAdd
import Order.Antisymmetrization
import SetTheory.Ordinal.Basic

#align_import data.dfinsupp.well_founded from "leanprover-community/mathlib"@"1dac236edca9b4b6f5f00b1ad831e35f89472837"

/-!
# Well-foundedness of the lexicographic and product orders on `dfinsupp` and `pi`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The primary results are `dfinsupp.lex.well_founded` and the two variants that follow it,
which essentially say that if `(>)` is a well order on `ι`, `(<)` is well-founded on each
`α i`, and `0` is a bottom element in `α i`, then the lexicographic `(<)` is well-founded
on `Π₀ i, α i`. The proof is modelled on the proof of `well_founded.cut_expand`.

The results are used to prove `pi.lex.well_founded` and two variants, which say that if
`ι` is finite and equipped with a linear order and `(<)` is well-founded on each `α i`,
then the lexicographic `(<)` is well-founded on `Π i, α i`, and the same is true for
`Π₀ i, α i` (`dfinsupp.lex.well_founded_of_finite`), because `dfinsupp` is order-isomorphic
to `pi` when `ι` is finite.

Finally, we deduce `dfinsupp.well_founded_lt`, `pi.well_founded_lt`,
`dfinsupp.well_founded_lt_of_finite` and variants, which concern the product order
rather than the lexicographic one. An order on `ι` is not required in these results,
but we deduce them from the well-foundedness of the lexicographic order by choosing
a well order on `ι` so that the product order `(<)` becomes a subrelation
of the lexicographic `(<)`.

All results are provided in two forms whenever possible: a general form where the relations
can be arbitrary (not the `(<)` of a preorder, or not even transitive, etc.) and a specialized
form provided as `well_founded_lt` instances where the `(d)finsupp/pi` type (or their `lex`
type synonyms) carries a natural `(<)`.

Notice that the definition of `dfinsupp.lex` says that `x < y` according to `dfinsupp.lex r s`
iff there exists a coordinate `i : ι` such that `x i < y i` according to `s i`, and at all
`r`-smaller coordinates `j` (i.e. satisfying `r j i`), `x` remains unchanged relative to `y`;
in other words, coordinates `j` such that `¬ r j i` and `j ≠ i` are exactly where changes
can happen arbitrarily. This explains the appearance of `rᶜ ⊓ (≠)` in
`dfinsupp.acc_single` and `dfinsupp.well_founded`. When `r` is trichotomous (e.g. the `(<)`
of a linear order), `¬ r j i ∧ j ≠ i` implies `r i j`, so it suffices to require `r.swap`
to be well-founded.
-/


variable {ι : Type _} {α : ι → Type _}

namespace DFinsupp

variable [hz : ∀ i, Zero (α i)] (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop)

open Relation Prod

#print DFinsupp.lex_fibration /-
/-- This key lemma says that if a finitely supported dependent function `x₀` is obtained by merging
  two such functions `x₁` and `x₂`, and if we evolve `x₀` down the `dfinsupp.lex` relation one
  step and get `x`, we can always evolve one of `x₁` and `x₂` down the `dfinsupp.lex` relation
  one step while keeping the other unchanged, and merge them back (possibly in a different way)
  to get back `x`. In other words, the two parts evolve essentially independently under
  `dfinsupp.lex`. This is used to show that a function `x` is accessible if
  `dfinsupp.single i (x i)` is accessible for each `i` in the (finite) support of `x`
  (`dfinsupp.lex.acc_of_single`). -/
theorem lex_fibration [∀ (i) (s : Set ι), Decidable (i ∈ s)] :
    Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
      fun x => piecewise x.2.1 x.2.2 x.1 :=
  by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs
  classical
  on_goal 1 =>
    refine' ⟨⟨{j | r j i → j ∈ p}, piecewise x₁ x {j | r j i}, x₂⟩, game_add.fst ⟨i, _⟩, _⟩
  on_goal 3 =>
    refine' ⟨⟨{j | r j i ∧ j ∈ p}, x₁, piecewise x₂ x {j | r j i}⟩, game_add.snd ⟨i, _⟩, _⟩
  pick_goal 3
  iterate 2 
    simp_rw [piecewise_apply]
    refine' ⟨fun j h => if_pos h, _⟩
    convert hs
    refine' ite_eq_right_iff.2 fun h' => (hr i h').symm ▸ _
    first
    | rw [if_neg h]
    | rw [if_pos h]
  all_goals ext j; simp_rw [piecewise_apply]; split_ifs with h₁ h₂
  · rw [hr j h₂, if_pos (h₁ h₂)]
  · rfl
  · rw [Set.mem_setOf, not_imp] at h₁; rw [hr j h₁.1, if_neg h₁.2]
  · rw [hr j h₁.1, if_pos h₁.2]
  · rw [hr j h₂, if_neg fun h' => h₁ ⟨h₂, h'⟩]
  · rfl
#align dfinsupp.lex_fibration DFinsupp.lex_fibration
-/

variable {r s}

#print DFinsupp.Lex.acc_of_single_erase /-
theorem Lex.acc_of_single_erase [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
    (hs : Acc (DFinsupp.Lex r s) <| single i (x i)) (hu : Acc (DFinsupp.Lex r s) <| x.eraseₓ i) :
    Acc (DFinsupp.Lex r s) x := by
  classical
  convert ←
    @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{i}, _⟩
      (InvImage.accessible snd <| hs.prod_game_add hu)
  convert piecewise_single_erase x i
#align dfinsupp.lex.acc_of_single_erase DFinsupp.Lex.acc_of_single_erase
-/

variable (hbot : ∀ ⦃i a⦄, ¬s i a 0)

#print DFinsupp.Lex.acc_zero /-
theorem Lex.acc_zero : Acc (DFinsupp.Lex r s) 0 :=
  Acc.intro 0 fun x ⟨_, _, h⟩ => (hbot h).elim
#align dfinsupp.lex.acc_zero DFinsupp.Lex.acc_zero
-/

#print DFinsupp.Lex.acc_of_single /-
theorem Lex.acc_of_single [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i) :
    (∀ i ∈ x.support, Acc (DFinsupp.Lex r s) <| single i (x i)) → Acc (DFinsupp.Lex r s) x :=
  by
  generalize ht : x.support = t; revert x
  classical
  induction' t using Finset.induction with b t hb ih
  · intro x ht; rw [support_eq_empty.1 ht]; exact fun _ => lex.acc_zero hbot
  refine' fun x ht h => lex.acc_of_single_erase b (h b <| t.mem_insert_self b) _
  refine' ih _ (by rw [support_erase, ht, Finset.erase_insert hb]) fun a ha => _
  rw [erase_ne (ha.ne_of_not_mem hb)]
  exact h a (Finset.mem_insert_of_mem ha)
#align dfinsupp.lex.acc_of_single DFinsupp.Lex.acc_of_single
-/

variable (hs : ∀ i, WellFounded (s i))

#print DFinsupp.Lex.acc_single /-
theorem Lex.acc_single [DecidableEq ι] {i : ι} (hi : Acc (rᶜ ⊓ (· ≠ ·)) i) :
    ∀ a, Acc (DFinsupp.Lex r s) (single i a) :=
  by
  induction' hi with i hi ih
  refine' fun a => (hs i).induction a fun a ha => _
  refine' Acc.intro _ fun x => _
  rintro ⟨k, hr, hs⟩
  classical
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  refine' lex.acc_of_single hbot x fun j hj => _
  obtain rfl | hij := eq_or_ne i j
  · exact ha _ hs
  by_cases r j i
  · rw [hr j h, single_eq_of_ne hij, single_zero]; exact lex.acc_zero hbot
  · exact ih _ ⟨h, hij.symm⟩ _
#align dfinsupp.lex.acc_single DFinsupp.Lex.acc_single
-/

#print DFinsupp.Lex.acc /-
theorem Lex.acc [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] (x : Π₀ i, α i)
    (h : ∀ i ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) i) : Acc (DFinsupp.Lex r s) x :=
  Lex.acc_of_single hbot x fun i hi => Lex.acc_single hbot hs (h i hi) _
#align dfinsupp.lex.acc DFinsupp.Lex.acc
-/

#print DFinsupp.Lex.wellFounded /-
theorem Lex.wellFounded (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (DFinsupp.Lex r s) :=
  ⟨fun x => by classical exact lex.acc hbot hs x fun i _ => hr.apply i⟩
#align dfinsupp.lex.well_founded DFinsupp.Lex.wellFounded
-/

#print DFinsupp.Lex.wellFounded' /-
theorem Lex.wellFounded' [IsTrichotomous ι r] (hr : WellFounded r.symm) :
    WellFounded (DFinsupp.Lex r s) :=
  Lex.wellFounded hbot hs <|
    Subrelation.wf
      (fun i j h => ((@IsTrichotomous.trichotomous ι r _ i j).resolve_left h.1).resolve_left h.2) hr
#align dfinsupp.lex.well_founded' DFinsupp.Lex.wellFounded'
-/

#print DFinsupp.Lex.wellFoundedLT /-
instance Lex.wellFoundedLT [LT ι] [IsTrichotomous ι (· < ·)] [hι : WellFoundedGT ι]
    [∀ i, CanonicallyOrderedAddCommMonoid (α i)] [hα : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨Lex.wellFounded' (fun i a => (zero_le a).not_lt) (fun i => (hα i).wf) hι.wf⟩
#align dfinsupp.lex.well_founded_lt DFinsupp.Lex.wellFoundedLT
-/

end DFinsupp

open DFinsupp

variable (r : ι → ι → Prop) {s : ∀ i, α i → α i → Prop}

#print Pi.Lex.wellFounded /-
theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : ∀ i, WellFounded (s i)) :
    WellFounded (Pi.Lex r s) :=
  by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
  · convert empty_wf; ext1 x; exact (h.1 x).elim
  letI : ∀ i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  haveI := IsTrans.swap r; haveI := IsIrrefl.swap r; haveI := Fintype.ofFinite ι
  refine' InvImage.wf equiv_fun_on_fintype.symm (lex.well_founded' (fun i a => _) hs _)
  exacts [(hs i).not_lt_min ⊤ _ trivial, Finite.wellFounded_of_trans_of_irrefl r.swap]
#align pi.lex.well_founded Pi.Lex.wellFounded
-/

#print Pi.Lex.wellFoundedLT /-
instance Pi.Lex.wellFoundedLT [LinearOrder ι] [Finite ι] [∀ i, LT (α i)]
    [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (∀ i, α i)) :=
  ⟨Pi.Lex.wellFounded (· < ·) fun i => (hwf i).1⟩
#align pi.lex.well_founded_lt Pi.Lex.wellFoundedLT
-/

#print Function.Lex.wellFoundedLT /-
instance Function.Lex.wellFoundedLT {α} [LinearOrder ι] [Finite ι] [LT α] [WellFoundedLT α] :
    WellFoundedLT (Lex (ι → α)) :=
  Pi.Lex.wellFoundedLT
#align function.lex.well_founded_lt Function.Lex.wellFoundedLT
-/

#print DFinsupp.Lex.wellFounded_of_finite /-
theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [∀ i, Zero (α i)]
    (hs : ∀ i, WellFounded (s i)) : WellFounded (DFinsupp.Lex r s) :=
  have := Fintype.ofFinite ι
  InvImage.wf equiv_fun_on_fintype (Pi.Lex.wellFounded r hs)
#align dfinsupp.lex.well_founded_of_finite DFinsupp.Lex.wellFounded_of_finite
-/

#print DFinsupp.Lex.wellFoundedLT_of_finite /-
instance DFinsupp.Lex.wellFoundedLT_of_finite [LinearOrder ι] [Finite ι] [∀ i, Zero (α i)]
    [∀ i, LT (α i)] [hwf : ∀ i, WellFoundedLT (α i)] : WellFoundedLT (Lex (Π₀ i, α i)) :=
  ⟨DFinsupp.Lex.wellFounded_of_finite (· < ·) fun i => (hwf i).1⟩
#align dfinsupp.lex.well_founded_lt_of_finite DFinsupp.Lex.wellFoundedLT_of_finite
-/

#print DFinsupp.wellFoundedLT /-
protected theorem DFinsupp.wellFoundedLT [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] (hbot : ∀ ⦃i⦄ ⦃a : α i⦄, ¬a < 0) : WellFoundedLT (Π₀ i, α i) :=
  ⟨by
    letI : ∀ i, Zero (Antisymmetrization (α i) (· ≤ ·)) := fun i => ⟨toAntisymmetrization (· ≤ ·) 0⟩
    let f := map_range (fun i => @toAntisymmetrization (α i) (· ≤ ·) _) fun i => rfl
    refine' Subrelation.wf (fun x y h => _) (InvImage.wf f <| lex.well_founded' _ (fun i => _) _)
    · exact well_ordering_rel.swap; · exact fun i => (· < ·)
    · haveI := IsStrictOrder.swap (@WellOrderingRel ι)
      obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder well_ordering_rel.swap h
      exact ⟨i, fun j hj => Quot.sound (he j hj), hl⟩
    · rintro i ⟨a⟩; apply hbot
    exacts [IsWellFounded.wf, IsTrichotomous.swap _, IsWellFounded.wf]⟩
#align dfinsupp.well_founded_lt DFinsupp.wellFoundedLT
-/

#print DFinsupp.wellFoundedLT' /-
instance DFinsupp.wellFoundedLT' [∀ i, CanonicallyOrderedAddCommMonoid (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  DFinsupp.wellFoundedLT fun i a => (zero_le a).not_lt
#align dfinsupp.well_founded_lt' DFinsupp.wellFoundedLT'
-/

#print Pi.wellFoundedLT /-
instance Pi.wellFoundedLT [Finite ι] [∀ i, Preorder (α i)] [hw : ∀ i, WellFoundedLT (α i)] :
    WellFoundedLT (∀ i, α i) :=
  ⟨by
    obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
    · convert empty_wf; ext1 x; exact (h.1 x).elim
    letI : ∀ i, Zero (α i) := fun i => ⟨(hw i).wf.min ⊤ ⟨x i, trivial⟩⟩
    haveI := Fintype.ofFinite ι
    refine' InvImage.wf equiv_fun_on_fintype.symm (DFinsupp.wellFoundedLT fun i a => _).wf
    exact (hw i).wf.not_lt_min ⊤ _ trivial⟩
#align pi.well_founded_lt Pi.wellFoundedLT
-/

#print Function.wellFoundedLT /-
instance Function.wellFoundedLT {α} [Finite ι] [Preorder α] [WellFoundedLT α] :
    WellFoundedLT (ι → α) :=
  Pi.wellFoundedLT
#align function.well_founded_lt Function.wellFoundedLT
-/

#print DFinsupp.wellFoundedLT_of_finite /-
instance DFinsupp.wellFoundedLT_of_finite [Finite ι] [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] : WellFoundedLT (Π₀ i, α i) :=
  have := Fintype.ofFinite ι
  ⟨InvImage.wf equiv_fun_on_fintype pi.well_founded_lt.wf⟩
#align dfinsupp.well_founded_lt_of_finite DFinsupp.wellFoundedLT_of_finite
-/

