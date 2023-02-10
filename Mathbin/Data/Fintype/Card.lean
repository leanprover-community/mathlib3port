/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.card
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Finset.Card
import Mathbin.Data.List.NodupEquivFin
import Mathbin.Tactic.Positivity
import Mathbin.Tactic.Wlog

/-!
# Cardinalities of finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main declarations

* `fintype.card α`: Cardinality of a fintype. Equal to `finset.univ.card`.
* `fintype.trunc_equiv_fin`: A fintype `α` is computably equivalent to `fin (card α)`. The
  `trunc`-free, noncomputable version is `fintype.equiv_fin`.
* `fintype.trunc_equiv_of_card_eq` `fintype.equiv_of_card_eq`: Two fintypes of same cardinality are
  equivalent. See above.
* `fin.equiv_iff_eq`: `fin m ≃ fin n` iff `m = n`.
* `infinite.nat_embedding`: An embedding of `ℕ` into an infinite type.

We also provide the following versions of the pigeonholes principle.
* `fintype.exists_ne_map_eq_of_card_lt` and `is_empty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `finite.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `finite.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `data.fintype.card_embedding`.

Types which have an injection from/a surjection to an `infinite` type are themselves `infinite`.
See `infinite.of_injective` and `infinite.of_surjective`.

## Instances

We provide `infinite` instances for
* specific types: `ℕ`, `ℤ`
* type constructors: `multiset α`, `list α`

-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function

namespace Fintype

#print Fintype.card /-
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
#align fintype.card Fintype.card
-/

#print Fintype.truncEquivFin /-
/-- There is (computably) an equivalence between `α` and `fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `trunc` to
preserve computability.

See `fintype.equiv_fin` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.

See `fintype.trunc_fin_bijection` for a version without `[decidable_eq α]`.
-/
def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α)) :=
  by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton' (@univ α _).1
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2
#align fintype.trunc_equiv_fin Fintype.truncEquivFin
-/

#print Fintype.equivFin /-
/-- There is (noncomputably) an equivalence between `α` and `fin (card α)`.

See `fintype.trunc_equiv_fin` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (trunc_equiv_fin α).out
#align fintype.equiv_fin Fintype.equivFin
-/

#print Fintype.truncFinBijection /-
/-- There is (computably) a bijection between `fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `trunc` to
preserve computability.

See `fintype.trunc_equiv_fin` for a version that gives an equivalence
given `[decidable_eq α]`.
-/
def truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) → α // Bijective f } :=
  by
  dsimp only [card, Finset.card]
  exact
    Quot.recOnSubsingleton' (@univ α _).1
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getBijectionOfForallMemList _ h))
      mem_univ_val univ.2
#align fintype.trunc_fin_bijection Fintype.truncFinBijection
-/

#print Fintype.subtype_card /-
theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = s.card :=
  Multiset.card_pmap _ _ _
#align fintype.subtype_card Fintype.subtype_card
-/

#print Fintype.card_of_subtype /-
theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = s.card :=
  by
  rw [← subtype_card s H]
  congr
#align fintype.card_of_subtype Fintype.card_of_subtype
-/

#print Fintype.card_ofFinset /-
@[simp]
theorem card_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Fintype.card p (ofFinset s H) = s.card :=
  Fintype.subtype_card s H
#align fintype.card_of_finset Fintype.card_ofFinset
-/

#print Fintype.card_of_finset' /-
theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] :
    Fintype.card p = s.card := by rw [← card_of_finset s H] <;> congr
#align fintype.card_of_finset' Fintype.card_of_finset'
-/

end Fintype

namespace Fintype

/- warning: fintype.of_equiv_card -> Fintype.ofEquiv_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] (f : Equiv.{succ u1, succ u2} α β), Eq.{1} Nat (Fintype.card.{u2} β (Fintype.ofEquiv.{u2, u1} β α _inst_1 f)) (Fintype.card.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] (f : Equiv.{succ u2, succ u1} α β), Eq.{1} Nat (Fintype.card.{u1} β (Fintype.ofEquiv.{u1, u2} β α _inst_1 f)) (Fintype.card.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align fintype.of_equiv_card Fintype.ofEquiv_cardₓ'. -/
theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _
#align fintype.of_equiv_card Fintype.ofEquiv_card

/- warning: fintype.card_congr -> Fintype.card_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], (Equiv.{succ u1, succ u2} α β) -> (Eq.{1} Nat (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], (Equiv.{succ u2, succ u1} α β) -> (Eq.{1} Nat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_congr Fintype.card_congrₓ'. -/
theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← of_equiv_card f] <;> congr
#align fintype.card_congr Fintype.card_congr

#print Fintype.card_congr' /-
@[congr]
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])
#align fintype.card_congr' Fintype.card_congr'
-/

section

variable [Fintype α] [Fintype β]

#print Fintype.truncEquivFinOfCardEq /-
/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `fin n`.

See `fintype.equiv_fin_of_card_eq` for the noncomputable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
def truncEquivFinOfCardEq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Fin n) :=
  (truncEquivFin α).map fun e => e.trans (Fin.cast h).toEquiv
#align fintype.trunc_equiv_fin_of_card_eq Fintype.truncEquivFinOfCardEq
-/

#print Fintype.equivFinOfCardEq /-
/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `fin n`.

See `fintype.trunc_equiv_fin_of_card_eq` for the computable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n :=
  letI := Classical.decEq α
  (trunc_equiv_fin_of_card_eq h).out
#align fintype.equiv_fin_of_card_eq Fintype.equivFinOfCardEq
-/

#print Fintype.truncEquivOfCardEq /-
/-- Two `fintype`s with the same cardinality are (computably) in bijection.

See `fintype.equiv_of_card_eq` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm
#align fintype.trunc_equiv_of_card_eq Fintype.truncEquivOfCardEq
-/

#print Fintype.equivOfCardEq /-
/-- Two `fintype`s with the same cardinality are (noncomputably) in bijection.

See `fintype.trunc_equiv_of_card_eq` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β :=
  by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (trunc_equiv_of_card_eq h).out
#align fintype.equiv_of_card_eq Fintype.equivOfCardEq
-/

end

/- warning: fintype.card_eq -> Fintype.card_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [F : Fintype.{u1} α] [G : Fintype.{u2} β], Iff (Eq.{1} Nat (Fintype.card.{u1} α F) (Fintype.card.{u2} β G)) (Nonempty.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [F : Fintype.{u2} α] [G : Fintype.{u1} β], Iff (Eq.{1} Nat (Fintype.card.{u2} α F) (Fintype.card.{u1} β G)) (Nonempty.{max (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} α β))
Case conversion may be inaccurate. Consider using '#align fintype.card_eq Fintype.card_eqₓ'. -/
theorem card_eq {α β} [F : Fintype α] [G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h =>
    haveI := Classical.propDecidable
    (trunc_equiv_of_card_eq h).Nonempty,
    fun ⟨f⟩ => card_congr f⟩
#align fintype.card_eq Fintype.card_eq

#print Fintype.card_ofSubsingleton /-
/-- Note: this lemma is specifically about `fintype.of_subsingleton`. For a statement about
arbitrary `fintype` instances, use either `fintype.card_le_one_iff_subsingleton` or
`fintype.card_unique`. -/
@[simp]
theorem card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl
#align fintype.card_of_subsingleton Fintype.card_ofSubsingleton
-/

#print Fintype.card_unique /-
@[simp]
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _
#align fintype.card_unique Fintype.card_unique
-/

#print Fintype.card_of_isEmpty /-
/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `fintype.card_eq_zero_iff`. -/
@[simp]
theorem card_of_isEmpty [IsEmpty α] : Fintype.card α = 0 :=
  rfl
#align fintype.card_of_is_empty Fintype.card_of_isEmpty
-/

end Fintype

namespace Set

variable {s t : Set α}

#print Set.toFinset_card /-
-- We use an arbitrary `[fintype s]` instance here,
-- not necessarily coming from a `[fintype α]`.
@[simp]
theorem toFinset_card {α : Type _} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val
#align set.to_finset_card Set.toFinset_card
-/

end Set

#print Finset.card_univ /-
theorem Finset.card_univ [Fintype α] : (Finset.univ : Finset α).card = Fintype.card α :=
  rfl
#align finset.card_univ Finset.card_univ
-/

#print Finset.eq_univ_of_card /-
theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : s.card = Fintype.card α) :
    s = univ :=
  eq_of_subset_of_card_le (subset_univ _) <| by rw [hs, Finset.card_univ]
#align finset.eq_univ_of_card Finset.eq_univ_of_card
-/

#print Finset.card_eq_iff_eq_univ /-
theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) :
    s.card = Fintype.card α ↔ s = Finset.univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩
#align finset.card_eq_iff_eq_univ Finset.card_eq_iff_eq_univ
-/

#print Finset.card_le_univ /-
theorem Finset.card_le_univ [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α :=
  card_le_of_subset (subset_univ s)
#align finset.card_le_univ Finset.card_le_univ
-/

#print Finset.card_lt_univ_of_not_mem /-
theorem Finset.card_lt_univ_of_not_mem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) :
    s.card < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩
#align finset.card_lt_univ_of_not_mem Finset.card_lt_univ_of_not_mem
-/

#print Finset.card_lt_iff_ne_univ /-
theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) :
    s.card < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)
#align finset.card_lt_iff_ne_univ Finset.card_lt_iff_ne_univ
-/

/- warning: finset.card_compl_lt_iff_nonempty -> Finset.card_compl_lt_iff_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (LT.lt.{0} Nat Nat.hasLt (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (Fintype.card.{u1} α _inst_1)) (Finset.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (LT.lt.{0} Nat instLTNat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (Fintype.card.{u1} α _inst_1)) (Finset.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.card_compl_lt_iff_nonempty Finset.card_compl_lt_iff_nonemptyₓ'. -/
theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    sᶜ.card < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty
#align finset.card_compl_lt_iff_nonempty Finset.card_compl_lt_iff_nonempty

#print Finset.card_univ_diff /-
theorem Finset.card_univ_diff [DecidableEq α] [Fintype α] (s : Finset α) :
    (Finset.univ \ s).card = Fintype.card α - s.card :=
  Finset.card_sdiff (subset_univ s)
#align finset.card_univ_diff Finset.card_univ_diff
-/

/- warning: finset.card_compl -> Finset.card_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u1} α _inst_2) (Finset.card.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u1} α _inst_2) (Finset.card.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.card_compl Finset.card_complₓ'. -/
theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) :
    sᶜ.card = Fintype.card α - s.card :=
  Finset.card_univ_diff s
#align finset.card_compl Finset.card_compl

/- warning: fintype.card_compl_set -> Fintype.card_compl_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (s : Set.{u1} α) [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))], Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u1} α _inst_1) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (s : Set.{u1} α) [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))], Eq.{1} Nat (Fintype.card.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) _inst_3) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u1} α _inst_1) (Fintype.card.{u1} (Set.Elem.{u1} α s) _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_compl_set Fintype.card_compl_setₓ'. -/
theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype ↥(sᶜ)] :
    Fintype.card ↥(sᶜ) = Fintype.card α - Fintype.card s := by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]
#align fintype.card_compl_set Fintype.card_compl_set

#print Fintype.card_fin /-
@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
  List.length_finRange n
#align fintype.card_fin Fintype.card_fin
-/

#print Finset.card_fin /-
@[simp]
theorem Finset.card_fin (n : ℕ) : Finset.card (Finset.univ : Finset (Fin n)) = n := by
  rw [Finset.card_univ, Fintype.card_fin]
#align finset.card_fin Finset.card_fin
-/

#print fin_injective /-
/-- `fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
theorem fin_injective : Function.Injective Fin := fun m n h =>
  (Fintype.card_fin m).symm.trans <| (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)
#align fin_injective fin_injective
-/

/- warning: fin.cast_eq_cast' -> Fin.cast_eq_cast' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat} (h : Eq.{2} Type (Fin n) (Fin m)), Eq.{1} ((Fin n) -> (Fin m)) (cast.{1} (Fin n) (Fin m) h) (coeFn.{1, 1} (OrderIso.{0, 0} (Fin n) (Fin m) (Fin.hasLe n) (Fin.hasLe m)) (fun (_x : RelIso.{0, 0} (Fin n) (Fin m) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin m) (Fin.hasLe m))) => (Fin n) -> (Fin m)) (RelIso.hasCoeToFun.{0, 0} (Fin n) (Fin m) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin m) (Fin.hasLe m))) (Fin.cast n m (fin_injective n m h)))
but is expected to have type
  forall {n : Nat} {m : Nat} (h : Eq.{2} Type (Fin n) (Fin m)), Eq.{1} ((Fin n) -> (Fin m)) (cast.{1} (Fin n) (Fin m) h) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin m)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin m) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin m)) (Fin n) (Fin m) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin m))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin m) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} (Fin n) (Fin m) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (Fin.cast n m (fin_injective n m h)))))
Case conversion may be inaccurate. Consider using '#align fin.cast_eq_cast' Fin.cast_eq_cast'ₓ'. -/
/-- A reversed version of `fin.cast_eq_cast` that is easier to rewrite with. -/
theorem Fin.cast_eq_cast' {n m : ℕ} (h : Fin n = Fin m) : cast h = ⇑(Fin.cast <| fin_injective h) :=
  (Fin.cast_eq_cast _).symm
#align fin.cast_eq_cast' Fin.cast_eq_cast'

#print card_finset_fin_le /-
theorem card_finset_fin_le {n : ℕ} (s : Finset (Fin n)) : s.card ≤ n := by
  simpa only [Fintype.card_fin] using s.card_le_univ
#align card_finset_fin_le card_finset_fin_le
-/

#print Fin.equiv_iff_eq /-
theorem Fin.equiv_iff_eq {m n : ℕ} : Nonempty (Fin m ≃ Fin n) ↔ m = n :=
  ⟨fun ⟨h⟩ => by simpa using Fintype.card_congr h, fun h => ⟨Equiv.cast <| h ▸ rfl⟩⟩
#align fin.equiv_iff_eq Fin.equiv_iff_eq
-/

#print Fintype.card_subtype_eq /-
@[simp]
theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] :
    Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique
#align fintype.card_subtype_eq Fintype.card_subtype_eq
-/

#print Fintype.card_subtype_eq' /-
@[simp]
theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] :
    Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique
#align fintype.card_subtype_eq' Fintype.card_subtype_eq'
-/

#print Fintype.card_empty /-
@[simp]
theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl
#align fintype.card_empty Fintype.card_empty
-/

#print Fintype.card_pempty /-
@[simp]
theorem Fintype.card_pempty : Fintype.card PEmpty = 0 :=
  rfl
#align fintype.card_pempty Fintype.card_pempty
-/

/- warning: fintype.card_unit -> Fintype.card_unit is a dubious translation:
lean 3 declaration is
  Eq.{1} Nat (Fintype.card.{0} Unit PUnit.fintype.{0}) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  Eq.{1} Nat (Fintype.card.{0} Unit instFintypePUnit.{0}) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align fintype.card_unit Fintype.card_unitₓ'. -/
theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl
#align fintype.card_unit Fintype.card_unit

/- warning: fintype.card_punit -> Fintype.card_punit is a dubious translation:
lean 3 declaration is
  Eq.{1} Nat (Fintype.card.{u1} PUnit.{succ u1} PUnit.fintype.{u1}) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  Eq.{1} Nat (Fintype.card.{u1} PUnit.{succ u1} instFintypePUnit.{u1}) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align fintype.card_punit Fintype.card_punitₓ'. -/
@[simp]
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl
#align fintype.card_punit Fintype.card_punit

#print Fintype.card_bool /-
@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl
#align fintype.card_bool Fintype.card_bool
-/

/- warning: fintype.card_ulift -> Fintype.card_ulift is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Eq.{1} Nat (Fintype.card.{max u1 u2} (ULift.{u2, u1} α) (ULift.fintype.{u1, u2} α _inst_1)) (Fintype.card.{u1} α _inst_1)
but is expected to have type
  forall (α : Type.{u2}) [_inst_1 : Fintype.{u2} α], Eq.{1} Nat (Fintype.card.{max u2 u1} (ULift.{u1, u2} α) (instFintypeULift.{u2, u1} α _inst_1)) (Fintype.card.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align fintype.card_ulift Fintype.card_uliftₓ'. -/
@[simp]
theorem Fintype.card_ulift (α : Type _) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.ofEquiv_card _
#align fintype.card_ulift Fintype.card_ulift

#print Fintype.card_plift /-
@[simp]
theorem Fintype.card_plift (α : Type _) [Fintype α] : Fintype.card (PLift α) = Fintype.card α :=
  Fintype.ofEquiv_card _
#align fintype.card_plift Fintype.card_plift
-/

#print Fintype.card_orderDual /-
@[simp]
theorem Fintype.card_orderDual (α : Type _) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl
#align fintype.card_order_dual Fintype.card_orderDual
-/

#print Fintype.card_lex /-
@[simp]
theorem Fintype.card_lex (α : Type _) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl
#align fintype.card_lex Fintype.card_lex
-/

#print Fintype.sumLeft /-
/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def Fintype.sumLeft {α β} [Fintype (Sum α β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → Sum α β) Sum.inl_injective
#align fintype.sum_left Fintype.sumLeft
-/

#print Fintype.sumRight /-
/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def Fintype.sumRight {α β} [Fintype (Sum α β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → Sum α β) Sum.inr_injective
#align fintype.sum_right Fintype.sumRight
-/

/-!
### Relation to `finite`

In this section we prove that `α : Type*` is `finite` if and only if `fintype α` is nonempty.
-/


#print Fintype.finite /-
@[nolint fintype_finite]
protected theorem Fintype.finite {α : Type _} (h : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩
#align fintype.finite Fintype.finite
-/

#print Finite.of_fintype /-
/-- For efficiency reasons, we want `finite` instances to have higher
priority than ones coming from `fintype` instances. -/
@[nolint fintype_finite]
instance (priority := 900) Finite.of_fintype (α : Type _) [Fintype α] : Finite α :=
  Fintype.finite ‹_›
#align finite.of_fintype Finite.of_fintype
-/

#print finite_iff_nonempty_fintype /-
theorem finite_iff_nonempty_fintype (α : Type _) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun h =>
    let ⟨k, ⟨e⟩⟩ := @Finite.exists_equiv_fin α h
    ⟨Fintype.ofEquiv _ e.symm⟩,
    fun ⟨_⟩ => inferInstance⟩
#align finite_iff_nonempty_fintype finite_iff_nonempty_fintype
-/

#print nonempty_fintype /-
/-- See also `nonempty_encodable`, `nonempty_denumerable`. -/
theorem nonempty_fintype (α : Type _) [Finite α] : Nonempty (Fintype α) :=
  (finite_iff_nonempty_fintype α).mp ‹_›
#align nonempty_fintype nonempty_fintype
-/

#print Fintype.ofFinite /-
/-- Noncomputably get a `fintype` instance from a `finite` instance. This is not an
instance because we want `fintype` instances to be useful for computations. -/
noncomputable def Fintype.ofFinite (α : Type _) [Finite α] : Fintype α :=
  (nonempty_fintype α).some
#align fintype.of_finite Fintype.ofFinite
-/

/- warning: finite.of_injective -> Finite.of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u2} β] (f : α -> β), (Function.Injective.{u1, u2} α β f) -> (Finite.{u1} α)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Finite.{u1} β] (f : α -> β), (Function.Injective.{u2, u1} α β f) -> (Finite.{u2} α)
Case conversion may be inaccurate. Consider using '#align finite.of_injective Finite.of_injectiveₓ'. -/
theorem Finite.of_injective {α β : Sort _} [Finite β] (f : α → β) (H : Injective f) : Finite α :=
  by
  cases nonempty_fintype (PLift β)
  rw [← Equiv.injective_comp Equiv.plift f, ← Equiv.comp_injective _ equiv.plift.symm] at H
  haveI := Fintype.ofInjective _ H
  exact Finite.of_equiv _ Equiv.plift
#align finite.of_injective Finite.of_injective

/- warning: finite.of_surjective -> Finite.of_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u1} α] (f : α -> β), (Function.Surjective.{u1, u2} α β f) -> (Finite.{u2} β)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Finite.{u2} α] (f : α -> β), (Function.Surjective.{u2, u1} α β f) -> (Finite.{u1} β)
Case conversion may be inaccurate. Consider using '#align finite.of_surjective Finite.of_surjectiveₓ'. -/
theorem Finite.of_surjective {α β : Sort _} [Finite α] (f : α → β) (H : Surjective f) : Finite β :=
  Finite.of_injective _ <| injective_surjInv H
#align finite.of_surjective Finite.of_surjective

#print Finite.exists_univ_list /-
theorem Finite.exists_univ_list (α) [Finite α] : ∃ l : List α, l.Nodup ∧ ∀ x : α, x ∈ l :=
  by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro univ.2 mem_univ_val
  exact ⟨_, by rwa [← e] at this⟩
#align finite.exists_univ_list Finite.exists_univ_list
-/

#print List.Nodup.length_le_card /-
theorem List.Nodup.length_le_card {α : Type _} [Fintype α] {l : List α} (h : l.Nodup) :
    l.length ≤ Fintype.card α := by
  classical exact List.toFinset_card_of_nodup h ▸ l.to_finset.card_le_univ
#align list.nodup.length_le_card List.Nodup.length_le_card
-/

namespace Fintype

variable [Fintype α] [Fintype β]

/- warning: fintype.card_le_of_injective -> Fintype.card_le_of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), (Function.Injective.{succ u2, succ u1} α β f) -> (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_le_of_injective Fintype.card_le_of_injectiveₓ'. -/
theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_inj_on f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h
#align fintype.card_le_of_injective Fintype.card_le_of_injective

/- warning: fintype.card_le_of_embedding -> Fintype.card_le_of_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], (Function.Embedding.{succ u1, succ u2} α β) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], (Function.Embedding.{succ u2, succ u1} α β) -> (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_le_of_embedding Fintype.card_le_of_embeddingₓ'. -/
theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2
#align fintype.card_le_of_embedding Fintype.card_le_of_embedding

/- warning: fintype.card_lt_of_injective_of_not_mem -> Fintype.card_lt_of_injective_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall {b : β}, (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f))) -> (LT.lt.{0} Nat Nat.hasLt (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), (Function.Injective.{succ u2, succ u1} α β f) -> (forall {b : β}, (Not (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.range.{u1, succ u2} β α f))) -> (LT.lt.{0} Nat instLTNat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align fintype.card_lt_of_injective_of_not_mem Fintype.card_lt_of_injective_of_not_memₓ'. -/
theorem card_lt_of_injective_of_not_mem (f : α → β) (h : Function.Injective f) {b : β}
    (w : b ∉ Set.range f) : card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
      Finset.card_lt_univ_of_not_mem <| by rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]
    
#align fintype.card_lt_of_injective_of_not_mem Fintype.card_lt_of_injective_of_not_mem

/- warning: fintype.card_lt_of_injective_not_surjective -> Fintype.card_lt_of_injective_not_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (Not (Function.Surjective.{succ u1, succ u2} α β f)) -> (LT.lt.{0} Nat Nat.hasLt (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), (Function.Injective.{succ u2, succ u1} α β f) -> (Not (Function.Surjective.{succ u2, succ u1} α β f)) -> (LT.lt.{0} Nat instLTNat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_lt_of_injective_not_surjective Fintype.card_lt_of_injective_not_surjectiveₓ'. -/
theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f)
    (h' : ¬Function.Surjective f) : card α < card β :=
  let ⟨y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_not_mem f h hy
#align fintype.card_lt_of_injective_not_surjective Fintype.card_lt_of_injective_not_surjective

/- warning: fintype.card_le_of_surjective -> Fintype.card_le_of_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), (Function.Surjective.{succ u1, succ u2} α β f) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u2} β _inst_2) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), (Function.Surjective.{succ u2, succ u1} α β f) -> (LE.le.{0} Nat instLENat (Fintype.card.{u1} β _inst_2) (Fintype.card.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align fintype.card_le_of_surjective Fintype.card_le_of_surjectiveₓ'. -/
theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surjInv h)
#align fintype.card_le_of_surjective Fintype.card_le_of_surjective

/- warning: fintype.card_range_le -> Fintype.card_range_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) [_inst_3 : Fintype.{u1} α] [_inst_4 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f))], LE.le.{0} Nat Nat.hasLe (Fintype.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) _inst_4) (Fintype.card.{u1} α _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u1} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f))], LE.le.{0} Nat instLENat (Fintype.card.{u1} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) _inst_4) (Fintype.card.{u2} α _inst_3)
Case conversion may be inaccurate. Consider using '#align fintype.card_range_le Fintype.card_range_leₓ'. -/
theorem card_range_le {α β : Type _} (f : α → β) [Fintype α] [Fintype (Set.range f)] :
    Fintype.card (Set.range f) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩
#align fintype.card_range_le Fintype.card_range_le

/- warning: fintype.card_range -> Fintype.card_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Type.{u3}} [_inst_3 : EmbeddingLike.{succ u3, succ u1, succ u2} F α β] (f : F) [_inst_4 : Fintype.{u1} α] [_inst_5 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{succ u3, succ u1, succ u2} F α β _inst_3)) f)))], Eq.{1} Nat (Fintype.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{succ u3, succ u1, succ u2} F α β _inst_3)) f))) _inst_5) (Fintype.card.{u1} α _inst_4)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {F : Type.{u1}} [_inst_3 : EmbeddingLike.{succ u1, succ u3, succ u2} F α β] (f : F) [_inst_4 : Fintype.{u3} α] [_inst_5 : Fintype.{u2} (Set.Elem.{u2} β (Set.range.{u2, succ u3} β α (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u3, succ u2} F α β _inst_3) f)))], Eq.{1} Nat (Fintype.card.{u2} (Set.Elem.{u2} β (Set.range.{u2, succ u3} β α (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u3, succ u2} F α β _inst_3) f))) _inst_5) (Fintype.card.{u3} α _inst_4)
Case conversion may be inaccurate. Consider using '#align fintype.card_range Fintype.card_rangeₓ'. -/
theorem card_range {α β F : Type _} [EmbeddingLike F α β] (f : F) [Fintype α]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective _ <| EmbeddingLike.injective f
#align fintype.card_range Fintype.card_range

#print Fintype.exists_ne_map_eq_of_card_lt /-
/-- The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ x y, x ≠ y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩
#align fintype.exists_ne_map_eq_of_card_lt Fintype.exists_ne_map_eq_of_card_lt
-/

#print Fintype.card_eq_one_iff /-
theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x := by
  rw [← card_unit, card_eq] <;>
    exact
      ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.Injective (Subsingleton.elim _ _)⟩, fun ⟨x, hx⟩ =>
        ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
            Subsingleton.elim _ _⟩⟩⟩
#align fintype.card_eq_one_iff Fintype.card_eq_one_iff
-/

#print Fintype.card_eq_zero_iff /-
theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card, Finset.card_eq_zero, univ_eq_empty_iff]
#align fintype.card_eq_zero_iff Fintype.card_eq_zero_iff
-/

#print Fintype.card_eq_zero /-
theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›
#align fintype.card_eq_zero Fintype.card_eq_zero
-/

#print Fintype.card_eq_one_iff_nonempty_unique /-
theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{  default := d
        uniq := h }⟩,
    fun ⟨h⟩ => Fintype.card_unique⟩
#align fintype.card_eq_one_iff_nonempty_unique Fintype.card_eq_one_iff_nonempty_unique
-/

#print Fintype.cardEqZeroEquivEquivEmpty /-
/-- A `fintype` with cardinality zero is equivalent to `empty`. -/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm
#align fintype.card_eq_zero_equiv_equiv_empty Fintype.cardEqZeroEquivEquivEmpty
-/

#print Fintype.card_pos_iff /-
theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  pos_iff_ne_zero.trans <| not_iff_comm.mp <| not_nonempty_iff.trans card_eq_zero_iff.symm
#align fintype.card_pos_iff Fintype.card_pos_iff
-/

#print Fintype.card_pos /-
theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h
#align fintype.card_pos Fintype.card_pos
-/

#print Fintype.card_ne_zero /-
theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  ne_of_gt card_pos
#align fintype.card_ne_zero Fintype.card_ne_zero
-/

#print Fintype.card_le_one_iff /-
theorem card_le_one_iff : card α ≤ 1 ↔ ∀ a b : α, a = b :=
  let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0 => fun ha =>
    ⟨fun h => fun a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succ _⟩
  | 1 => fun ha =>
    ⟨fun h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a, hx b], fun _ => ha ▸ le_rfl⟩
  | n + 2 => fun ha =>
    ⟨fun h => by rw [← ha] at h <;> exact absurd h (by decide), fun h =>
      card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩
#align fintype.card_le_one_iff Fintype.card_le_one_iff
-/

#print Fintype.card_le_one_iff_subsingleton /-
theorem card_le_one_iff_subsingleton : card α ≤ 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm
#align fintype.card_le_one_iff_subsingleton Fintype.card_le_one_iff_subsingleton
-/

#print Fintype.one_lt_card_iff_nontrivial /-
theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α := by
  classical
    rw [← not_iff_not]
    push_neg
    rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]
#align fintype.one_lt_card_iff_nontrivial Fintype.one_lt_card_iff_nontrivial
-/

#print Fintype.exists_ne_of_one_lt_card /-
theorem exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a
#align fintype.exists_ne_of_one_lt_card Fintype.exists_ne_of_one_lt_card
-/

#print Fintype.exists_pair_of_one_lt_card /-
theorem exists_pair_of_one_lt_card (h : 1 < card α) : ∃ a b : α, a ≠ b :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α
#align fintype.exists_pair_of_one_lt_card Fintype.exists_pair_of_one_lt_card
-/

#print Fintype.card_eq_one_of_forall_eq /-
theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩
#align fintype.card_eq_one_of_forall_eq Fintype.card_eq_one_of_forall_eq
-/

#print Fintype.one_lt_card /-
theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h
#align fintype.one_lt_card Fintype.one_lt_card
-/

#print Fintype.one_lt_card_iff /-
theorem one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff
#align fintype.one_lt_card_iff Fintype.one_lt_card_iff
-/

#print Fintype.two_lt_card_iff /-
theorem two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_and_iff]
#align fintype.two_lt_card_iff Fintype.two_lt_card_iff
-/

/- warning: fintype.card_of_bijective -> Fintype.card_of_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] {f : α -> β}, (Function.Bijective.{succ u1, succ u2} α β f) -> (Eq.{1} Nat (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] {f : α -> β}, (Function.Bijective.{succ u2, succ u1} α β f) -> (Eq.{1} Nat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_of_bijective Fintype.card_of_bijectiveₓ'. -/
theorem card_of_bijective {f : α → β} (hf : Bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)
#align fintype.card_of_bijective Fintype.card_of_bijective

end Fintype

namespace Finite

variable [Finite α]

#print Finite.injective_iff_surjective /-
theorem injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f := by
  haveI := Classical.propDecidable <;> cases nonempty_fintype α <;>
    exact
      have : ∀ {f : α → α}, injective f → surjective f := fun f hinj x =>
        have h₁ : image f univ = univ :=
          eq_of_subset_of_card_le (subset_univ _)
            ((card_image_of_injective univ hinj).symm ▸ le_rfl)
        have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ _
        exists_of_bex (mem_image.1 h₂)
      ⟨this, fun hsurj =>
        has_left_inverse.injective
          ⟨surj_inv hsurj,
            left_inverse_of_surjective_of_right_inverse (this (injective_surj_inv _))
              (right_inverse_surj_inv _)⟩⟩
#align finite.injective_iff_surjective Finite.injective_iff_surjective
-/

#print Finite.injective_iff_bijective /-
theorem injective_iff_bijective {f : α → α} : Injective f ↔ Bijective f := by
  simp [bijective, injective_iff_surjective]
#align finite.injective_iff_bijective Finite.injective_iff_bijective
-/

#print Finite.surjective_iff_bijective /-
theorem surjective_iff_bijective {f : α → α} : Surjective f ↔ Bijective f := by
  simp [bijective, injective_iff_surjective]
#align finite.surjective_iff_bijective Finite.surjective_iff_bijective
-/

/- warning: finite.injective_iff_surjective_of_equiv -> Finite.injective_iff_surjective_of_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] {f : α -> β}, (Equiv.{succ u1, succ u2} α β) -> (Iff (Function.Injective.{succ u1, succ u2} α β f) (Function.Surjective.{succ u1, succ u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u2} α] {f : α -> β}, (Equiv.{succ u2, succ u1} α β) -> (Iff (Function.Injective.{succ u2, succ u1} α β f) (Function.Surjective.{succ u2, succ u1} α β f))
Case conversion may be inaccurate. Consider using '#align finite.injective_iff_surjective_of_equiv Finite.injective_iff_surjective_of_equivₓ'. -/
theorem injective_iff_surjective_of_equiv {f : α → β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩
#align finite.injective_iff_surjective_of_equiv Finite.injective_iff_surjective_of_equiv

alias injective_iff_bijective ↔ _root_.function.injective.bijective_of_finite _
#align function.injective.bijective_of_finite Function.Injective.bijective_of_finite

alias surjective_iff_bijective ↔ _root_.function.surjective.bijective_of_finite _
#align function.surjective.bijective_of_finite Function.Surjective.bijective_of_finite

/- warning: function.injective.surjective_of_fintype -> Function.Injective.surjective_of_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] {f : α -> β}, (Equiv.{succ u1, succ u2} α β) -> (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Surjective.{succ u1, succ u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u2} α] {f : α -> β}, (Equiv.{succ u2, succ u1} α β) -> (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Surjective.{succ u2, succ u1} α β f)
Case conversion may be inaccurate. Consider using '#align function.injective.surjective_of_fintype Function.Injective.surjective_of_fintypeₓ'. -/
/- warning: function.surjective.injective_of_fintype -> Function.Surjective.injective_of_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] {f : α -> β}, (Equiv.{succ u1, succ u2} α β) -> (Function.Surjective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u1, succ u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u2} α] {f : α -> β}, (Equiv.{succ u2, succ u1} α β) -> (Function.Surjective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u2, succ u1} α β f)
Case conversion may be inaccurate. Consider using '#align function.surjective.injective_of_fintype Function.Surjective.injective_of_fintypeₓ'. -/
alias injective_iff_surjective_of_equiv ↔
  _root_.function.injective.surjective_of_fintype _root_.function.surjective.injective_of_fintype
#align function.injective.surjective_of_fintype Function.Injective.surjective_of_fintype
#align function.surjective.injective_of_fintype Function.Surjective.injective_of_fintype

end Finite

namespace Fintype

variable [Fintype α] [Fintype β]

/- warning: fintype.bijective_iff_injective_and_card -> Fintype.bijective_iff_injective_and_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), Iff (Function.Bijective.{succ u1, succ u2} α β f) (And (Function.Injective.{succ u1, succ u2} α β f) (Eq.{1} Nat (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), Iff (Function.Bijective.{succ u2, succ u1} α β f) (And (Function.Injective.{succ u2, succ u1} α β f) (Eq.{1} Nat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align fintype.bijective_iff_injective_and_card Fintype.bijective_iff_injective_and_cardₓ'. -/
theorem bijective_iff_injective_and_card (f : α → β) :
    Bijective f ↔ Injective f ∧ card α = card β :=
  ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
    ⟨h.1, h.1.surjective_of_fintype <| equivOfCardEq h.2⟩⟩
#align fintype.bijective_iff_injective_and_card Fintype.bijective_iff_injective_and_card

/- warning: fintype.bijective_iff_surjective_and_card -> Fintype.bijective_iff_surjective_and_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), Iff (Function.Bijective.{succ u1, succ u2} α β f) (And (Function.Surjective.{succ u1, succ u2} α β f) (Eq.{1} Nat (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), Iff (Function.Bijective.{succ u2, succ u1} α β f) (And (Function.Surjective.{succ u2, succ u1} α β f) (Eq.{1} Nat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align fintype.bijective_iff_surjective_and_card Fintype.bijective_iff_surjective_and_cardₓ'. -/
theorem bijective_iff_surjective_and_card (f : α → β) :
    Bijective f ↔ Surjective f ∧ card α = card β :=
  ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
    ⟨h.1.injective_of_fintype <| equivOfCardEq h.2, h.1⟩⟩
#align fintype.bijective_iff_surjective_and_card Fintype.bijective_iff_surjective_and_card

#print Function.LeftInverse.rightInverse_of_card_le /-
theorem Function.LeftInverse.rightInverse_of_card_le {f : α → β} {g : β → α} (hfg : LeftInverse f g)
    (hcard : card α ≤ card β) : RightInverse f g :=
  have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg
#align function.left_inverse.right_inverse_of_card_le Function.LeftInverse.rightInverse_of_card_le
-/

#print Function.RightInverse.leftInverse_of_card_le /-
theorem Function.RightInverse.leftInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : RightInverse f g) (hcard : card β ≤ card α) : LeftInverse f g :=
  Function.LeftInverse.rightInverse_of_card_le hfg hcard
#align function.right_inverse.left_inverse_of_card_le Function.RightInverse.leftInverse_of_card_le
-/

end Fintype

namespace Equiv

variable [Fintype α] [Fintype β]

open Fintype

#print Equiv.ofLeftInverseOfCardLe /-
/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofLeftInverseOfCardLe (hβα : card β ≤ card α) (f : α → β) (g : β → α) (h : LeftInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_card_le hβα
#align equiv.of_left_inverse_of_card_le Equiv.ofLeftInverseOfCardLe
-/

#print Equiv.ofRightInverseOfCardLe /-
/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofRightInverseOfCardLe (hαβ : card α ≤ card β) (f : α → β) (g : β → α) (h : RightInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h
#align equiv.of_right_inverse_of_card_le Equiv.ofRightInverseOfCardLe
-/

end Equiv

#print Fintype.card_coe /-
@[simp]
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = s.card :=
  Fintype.card_of_finset' s fun _ => Iff.rfl
#align fintype.card_coe Fintype.card_coe
-/

#print Finset.equivFin /-
/-- Noncomputable equivalence between a finset `s` coerced to a type and `fin s.card`. -/
noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin s.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)
#align finset.equiv_fin Finset.equivFin
-/

#print Finset.equivFinOfCardEq /-
/-- Noncomputable equivalence between a finset `s` as a fintype and `fin n`, when there is a
proof that `s.card = n`. -/
noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : s.card = n) : s ≃ Fin n :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)
#align finset.equiv_fin_of_card_eq Finset.equivFinOfCardEq
-/

#print Finset.equivOfCardEq /-
/-- Noncomputable equivalence between two finsets `s` and `t` as fintypes when there is a proof
that `s.card = t.card`.-/
noncomputable def Finset.equivOfCardEq {s t : Finset α} (h : s.card = t.card) : s ≃ t :=
  Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))
#align finset.equiv_of_card_eq Finset.equivOfCardEq
-/

#print Fintype.card_Prop /-
@[simp]
theorem Fintype.card_Prop : Fintype.card Prop = 2 :=
  rfl
#align fintype.card_Prop Fintype.card_Prop
-/

#print set_fintype_card_le_univ /-
theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype ↥s] :
    Fintype.card ↥s ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype s)
#align set_fintype_card_le_univ set_fintype_card_le_univ
-/

#print set_fintype_card_eq_univ_iff /-
theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype ↥s] :
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card, Finset.card_eq_iff_eq_univ, ← Set.toFinset_univ, Set.toFinset_inj]
#align set_fintype_card_eq_univ_iff set_fintype_card_eq_univ_iff
-/

namespace Function.Embedding

#print Function.Embedding.equivOfFintypeSelfEmbedding /-
/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
noncomputable def equivOfFintypeSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e e.2.bijective_of_finite
#align function.embedding.equiv_of_fintype_self_embedding Function.Embedding.equivOfFintypeSelfEmbedding
-/

#print Function.Embedding.equiv_of_fintype_self_embedding_to_embedding /-
@[simp]
theorem equiv_of_fintype_self_embedding_to_embedding [Finite α] (e : α ↪ α) :
    e.equivOfFintypeSelfEmbedding.toEmbedding = e :=
  by
  ext
  rfl
#align function.embedding.equiv_of_fintype_self_embedding_to_embedding Function.Embedding.equiv_of_fintype_self_embedding_to_embedding
-/

/- warning: function.embedding.is_empty_of_card_lt -> Function.Embedding.is_empty_of_card_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], (LT.lt.{0} Nat Nat.hasLt (Fintype.card.{u2} β _inst_2) (Fintype.card.{u1} α _inst_1)) -> (IsEmpty.{max 1 (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], (LT.lt.{0} Nat instLTNat (Fintype.card.{u1} β _inst_2) (Fintype.card.{u2} α _inst_1)) -> (IsEmpty.{max (succ u1) (succ u2)} (Function.Embedding.{succ u2, succ u1} α β))
Case conversion may be inaccurate. Consider using '#align function.embedding.is_empty_of_card_lt Function.Embedding.is_empty_of_card_ltₓ'. -/
/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp]
theorem is_empty_of_card_lt [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α) :
    IsEmpty (α ↪ β) :=
  ⟨fun f =>
    let ⟨x, y, Ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
    Ne <| f.Injective feq⟩
#align function.embedding.is_empty_of_card_lt Function.Embedding.is_empty_of_card_lt

#print Function.Embedding.truncOfCardLe /-
/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def truncOfCardLe [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α ≤ Fintype.card β) : Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLe h).toEmbedding.trans eb.symm.toEmbedding)
#align function.embedding.trunc_of_card_le Function.Embedding.truncOfCardLe
-/

/- warning: function.embedding.nonempty_of_card_le -> Function.Embedding.nonempty_of_card_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2)) -> (Nonempty.{max 1 (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2)) -> (Nonempty.{max (succ u1) (succ u2)} (Function.Embedding.{succ u2, succ u1} α β))
Case conversion may be inaccurate. Consider using '#align function.embedding.nonempty_of_card_le Function.Embedding.nonempty_of_card_leₓ'. -/
theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α ≤ Fintype.card β) :
    Nonempty (α ↪ β) := by classical exact (trunc_of_card_le h).Nonempty
#align function.embedding.nonempty_of_card_le Function.Embedding.nonempty_of_card_le

/- warning: function.embedding.nonempty_iff_card_le -> Function.Embedding.nonempty_iff_card_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], Iff (Nonempty.{max 1 (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β)) (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], Iff (Nonempty.{max (succ u1) (succ u2)} (Function.Embedding.{succ u2, succ u1} α β)) (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align function.embedding.nonempty_iff_card_le Function.Embedding.nonempty_iff_card_leₓ'. -/
theorem nonempty_iff_card_le [Fintype α] [Fintype β] :
    Nonempty (α ↪ β) ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩
#align function.embedding.nonempty_iff_card_le Function.Embedding.nonempty_iff_card_le

/- warning: function.embedding.exists_of_card_le_finset -> Function.Embedding.exists_of_card_le_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u2} β}, (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} α _inst_1) (Finset.card.{u2} β s)) -> (Exists.{max 1 (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (f : Function.Embedding.{succ u1, succ u2} α β) => HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] {s : Finset.{u1} β}, (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_1) (Finset.card.{u1} β s)) -> (Exists.{max (succ u2) (succ u1)} (Function.Embedding.{succ u2, succ u1} α β) (fun (f : Function.Embedding.{succ u2, succ u1} α β) => HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f)) (Finset.toSet.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align function.embedding.exists_of_card_le_finset Function.Embedding.exists_of_card_le_finsetₓ'. -/
theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α ≤ s.card) :
    ∃ f : α ↪ β, Set.range f ⊆ s :=
  by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact ⟨f.trans (embedding.subtype _), by simp [Set.range_subset_iff]⟩
#align function.embedding.exists_of_card_le_finset Function.Embedding.exists_of_card_le_finset

end Function.Embedding

#print Finset.univ_map_embedding /-
@[simp]
theorem Finset.univ_map_embedding {α : Type _} [Fintype α] (e : α ↪ α) : univ.map e = univ := by
  rw [← e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]
#align finset.univ_map_embedding Finset.univ_map_embedding
-/

namespace Fintype

/- warning: fintype.card_lt_of_surjective_not_injective -> Fintype.card_lt_of_surjective_not_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] (f : α -> β), (Function.Surjective.{succ u1, succ u2} α β f) -> (Not (Function.Injective.{succ u1, succ u2} α β f)) -> (LT.lt.{0} Nat Nat.hasLt (Fintype.card.{u2} β _inst_2) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] (f : α -> β), (Function.Surjective.{succ u2, succ u1} α β f) -> (Not (Function.Injective.{succ u2, succ u1} α β f)) -> (LT.lt.{0} Nat instLTNat (Fintype.card.{u1} β _inst_2) (Fintype.card.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align fintype.card_lt_of_surjective_not_injective Fintype.card_lt_of_surjective_not_injectiveₓ'. -/
theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α → β)
    (h : Function.Surjective f) (h' : ¬Function.Injective f) : card β < card α :=
  card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
    h' <| h.injective_of_fintype (Equiv.ofBijective _ w).symm
#align fintype.card_lt_of_surjective_not_injective Fintype.card_lt_of_surjective_not_injective

end Fintype

#print Fintype.card_subtype_le /-
theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)
#align fintype.card_subtype_le Fintype.card_subtype_le
-/

#print Fintype.card_subtype_lt /-
theorem Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [DecidablePred p] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_not_mem coe Subtype.coe_injective <| by
    rwa [Subtype.range_coe_subtype]
#align fintype.card_subtype_lt Fintype.card_subtype_lt
-/

#print Fintype.card_subtype /-
theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } = ((Finset.univ : Finset α).filterₓ p).card :=
  by
  refine' Fintype.card_of_subtype _ _
  simp
#align fintype.card_subtype Fintype.card_subtype
-/

#print Fintype.card_subtype_compl /-
@[simp]
theorem Fintype.card_subtype_compl [Fintype α] (p : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical rw [Fintype.card_of_subtype (Set.toFinset (pᶜ)), Set.toFinset_compl p,
            Finset.card_compl, Fintype.card_of_subtype (Set.toFinset p)] <;>
          intro <;>
        simp only [Set.mem_toFinset, Set.mem_compl_iff] <;>
      rfl
#align fintype.card_subtype_compl Fintype.card_subtype_compl
-/

#print Fintype.card_subtype_mono /-
theorem Fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q) [Fintype { x // p x }]
    [Fintype { x // q x }] : Fintype.card { x // p x } ≤ Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)
#align fintype.card_subtype_mono Fintype.card_subtype_mono
-/

#print Fintype.card_compl_eq_card_compl /-
/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem Fintype.card_compl_eq_card_compl [Finite α] (p q : α → Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }]
    (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } :=
  by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]
#align fintype.card_compl_eq_card_compl Fintype.card_compl_eq_card_compl
-/

#print Fintype.card_quotient_le /-
theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α → α → Prop)] : Fintype.card (Quotient s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ (surjective_quotient_mk _)
#align fintype.card_quotient_le Fintype.card_quotient_le
-/

#print Fintype.card_quotient_lt /-
theorem Fintype.card_quotient_lt [Fintype α] {s : Setoid α} [DecidableRel ((· ≈ ·) : α → α → Prop)]
    {x y : α} (h1 : x ≠ y) (h2 : x ≈ y) : Fintype.card (Quotient s) < Fintype.card α :=
  Fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _) fun w =>
    h1 (w <| Quotient.eq'.mpr h2)
#align fintype.card_quotient_lt Fintype.card_quotient_lt
-/

#print univ_eq_singleton_of_card_one /-
theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) :
    (univ : Finset α) = {x} := by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  apply le_of_eq
  simp [h, Finset.card_univ]
#align univ_eq_singleton_of_card_one univ_eq_singleton_of_card_one
-/

namespace Finite

variable [Finite α]

#print Finite.wellFounded_of_trans_of_irrefl /-
theorem wellFounded_of_trans_of_irrefl (r : α → α → Prop) [IsTrans α r] [IsIrrefl α r] :
    WellFounded r := by
  classical cases nonempty_fintype α <;>
      exact
        have :
          ∀ x y, r x y → (univ.filter fun z => r z x).card < (univ.filter fun z => r z y).card :=
          fun x y hxy =>
          Finset.card_lt_card <| by
            simp only [finset.lt_iff_ssubset.symm, lt_iff_le_not_le, Finset.le_iff_subset,
                Finset.subset_iff, mem_filter, true_and_iff, mem_univ, hxy] <;>
              exact
                ⟨fun z hzx => trans hzx hxy,
                  not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
        Subrelation.wf this (measure_wf _)
#align finite.well_founded_of_trans_of_irrefl Finite.wellFounded_of_trans_of_irrefl
-/

#print Finite.Preorder.wellFounded_lt /-
theorem Preorder.wellFounded_lt [Preorder α] : WellFounded ((· < ·) : α → α → Prop) :=
  wellFounded_of_trans_of_irrefl _
#align finite.preorder.well_founded_lt Finite.Preorder.wellFounded_lt
-/

#print Finite.Preorder.wellFounded_gt /-
theorem Preorder.wellFounded_gt [Preorder α] : WellFounded ((· > ·) : α → α → Prop) :=
  wellFounded_of_trans_of_irrefl _
#align finite.preorder.well_founded_gt Finite.Preorder.wellFounded_gt
-/

#print Finite.LinearOrder.isWellOrder_lt /-
instance (priority := 10) LinearOrder.isWellOrder_lt [LinearOrder α] : IsWellOrder α (· < ·)
    where wf := Preorder.wellFounded_lt
#align finite.linear_order.is_well_order_lt Finite.LinearOrder.isWellOrder_lt
-/

#print Finite.LinearOrder.isWellOrder_gt /-
instance (priority := 10) LinearOrder.isWellOrder_gt [LinearOrder α] : IsWellOrder α (· > ·)
    where wf := Preorder.wellFounded_gt
#align finite.linear_order.is_well_order_gt Finite.LinearOrder.isWellOrder_gt
-/

end Finite

#print Fintype.false /-
@[nolint fintype_finite]
protected theorem Fintype.false [Infinite α] (h : Fintype α) : False :=
  not_finite α
#align fintype.false Fintype.false
-/

#print is_empty_fintype /-
@[simp]
theorem is_empty_fintype {α : Type _} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.Finite⟩⟩
#align is_empty_fintype is_empty_fintype
-/

#print fintypeOfNotInfinite /-
/-- A non-infinite type is a fintype. -/
noncomputable def fintypeOfNotInfinite {α : Type _} (h : ¬Infinite α) : Fintype α :=
  @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)
#align fintype_of_not_infinite fintypeOfNotInfinite
-/

section

open Classical

#print fintypeOrInfinite /-
/-- Any type is (classically) either a `fintype`, or `infinite`.

One can obtain the relevant typeclasses via `cases fintype_or_infinite α; resetI`.
-/
noncomputable def fintypeOrInfinite (α : Type _) : PSum (Fintype α) (Infinite α) :=
  if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)
#align fintype_or_infinite fintypeOrInfinite
-/

end

/- warning: finset.exists_minimal -> Finset.exists_minimal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Finset.{u1} α), (Finset.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) m s) => forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x m)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Finset.{u1} α), (Finset.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) m s) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x m)))))
Case conversion may be inaccurate. Consider using '#align finset.exists_minimal Finset.exists_minimalₓ'. -/
theorem Finset.exists_minimal {α : Type _} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬x < m := by
  obtain ⟨c, hcs : c ∈ s⟩ := h
  have : WellFounded (@LT.lt { x // x ∈ s } _) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min Set.univ ⟨⟨c, hcs⟩, trivial⟩
  exact ⟨m, hms, fun x hx hxm => H ⟨x, hx⟩ trivial hxm⟩
#align finset.exists_minimal Finset.exists_minimal

/- warning: finset.exists_maximal -> Finset.exists_maximal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Finset.{u1} α), (Finset.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) m s) => forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) m x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Finset.{u1} α), (Finset.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) m s) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (Not (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) m x)))))
Case conversion may be inaccurate. Consider using '#align finset.exists_maximal Finset.exists_maximalₓ'. -/
theorem Finset.exists_maximal {α : Type _} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬m < x :=
  @Finset.exists_minimal αᵒᵈ _ s h
#align finset.exists_maximal Finset.exists_maximal

namespace Infinite

#print Infinite.of_not_fintype /-
theorem of_not_fintype (h : Fintype α → False) : Infinite α :=
  is_empty_fintype.mp ⟨h⟩
#align infinite.of_not_fintype Infinite.of_not_fintype
-/

#print Infinite.of_injective_to_set /-
/-- If `s : set α` is a proper subset of `α` and `f : α → s` is injective, then `α` is infinite. -/
theorem of_injective_to_set {s : Set α} (hs : s ≠ Set.univ) {f : α → s} (hf : Injective f) :
    Infinite α :=
  of_not_fintype fun h => by
    skip
    classical
      refine' lt_irrefl (Fintype.card α) _
      calc
        Fintype.card α ≤ Fintype.card s := Fintype.card_le_of_injective f hf
        _ = s.to_finset.card := s.to_finset_card.symm
        _ < Fintype.card α :=
          Finset.card_lt_card <| by rwa [Set.toFinset_ssubset_univ, Set.ssubset_univ_iff]
        
#align infinite.of_injective_to_set Infinite.of_injective_to_set
-/

#print Infinite.of_surjective_from_set /-
/-- If `s : set α` is a proper subset of `α` and `f : s → α` is surjective, then `α` is infinite. -/
theorem of_surjective_from_set {s : Set α} (hs : s ≠ Set.univ) {f : s → α} (hf : Surjective f) :
    Infinite α :=
  of_injective_to_set hs (injective_surjInv hf)
#align infinite.of_surjective_from_set Infinite.of_surjective_from_set
-/

#print Infinite.exists_not_mem_finset /-
theorem exists_not_mem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩
#align infinite.exists_not_mem_finset Infinite.exists_not_mem_finset
-/

-- see Note [lower instance priority]
instance (priority := 100) (α : Type _) [H : Infinite α] : Nontrivial α :=
  ⟨let ⟨x, hx⟩ := exists_not_mem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_not_mem_finset ({x} : Finset α)
    ⟨y, x, by simpa only [mem_singleton] using hy⟩⟩

#print Infinite.nonempty /-
protected theorem nonempty (α : Type _) [Infinite α] : Nonempty α := by infer_instance
#align infinite.nonempty Infinite.nonempty
-/

/- warning: infinite.of_injective -> Infinite.of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Infinite.{u2} β] (f : β -> α), (Function.Injective.{u2, u1} β α f) -> (Infinite.{u1} α)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Infinite.{u1} β] (f : β -> α), (Function.Injective.{u1, u2} β α f) -> (Infinite.{u2} α)
Case conversion may be inaccurate. Consider using '#align infinite.of_injective Infinite.of_injectiveₓ'. -/
theorem of_injective {α β} [Infinite β] (f : β → α) (hf : Injective f) : Infinite α :=
  ⟨fun I => (Finite.of_injective f hf).False⟩
#align infinite.of_injective Infinite.of_injective

/- warning: infinite.of_surjective -> Infinite.of_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Infinite.{u2} β] (f : α -> β), (Function.Surjective.{u1, u2} α β f) -> (Infinite.{u1} α)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Infinite.{u1} β] (f : α -> β), (Function.Surjective.{u2, u1} α β f) -> (Infinite.{u2} α)
Case conversion may be inaccurate. Consider using '#align infinite.of_surjective Infinite.of_surjectiveₓ'. -/
theorem of_surjective {α β} [Infinite β] (f : α → β) (hf : Surjective f) : Infinite α :=
  ⟨fun I => (Finite.of_surjective f hf).False⟩
#align infinite.of_surjective Infinite.of_surjective

end Infinite

instance : Infinite ℕ :=
  Infinite.of_not_fintype <| by
    intro h
    exact (Finset.range _).card_le_univ.not_lt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)

instance : Infinite ℤ :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj

instance [Nonempty α] : Infinite (Multiset α) :=
  let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)

instance [Nonempty α] : Infinite (List α) :=
  Infinite.of_surjective (coe : List α → Multiset α) (surjective_quot_mk _)

#print Infinite.set /-
instance Infinite.set [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective singleton Set.singleton_injective
#align infinite.set Infinite.set
-/

instance [Infinite α] : Infinite (Finset α) :=
  Infinite.of_injective singleton Finset.singleton_injective

instance [Infinite α] : Infinite (Option α) :=
  Infinite.of_injective some (Option.some_injective α)

#print Sum.infinite_of_left /-
instance Sum.infinite_of_left [Infinite α] : Infinite (Sum α β) :=
  Infinite.of_injective Sum.inl Sum.inl_injective
#align sum.infinite_of_left Sum.infinite_of_left
-/

#print Sum.infinite_of_right /-
instance Sum.infinite_of_right [Infinite β] : Infinite (Sum α β) :=
  Infinite.of_injective Sum.inr Sum.inr_injective
#align sum.infinite_of_right Sum.infinite_of_right
-/

#print Prod.infinite_of_right /-
instance Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.snd Prod.snd_surjective
#align prod.infinite_of_right Prod.infinite_of_right
-/

#print Prod.infinite_of_left /-
instance Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.fst Prod.fst_surjective
#align prod.infinite_of_left Prod.infinite_of_left
-/

namespace Infinite

private noncomputable def nat_embedding_aux (α : Type _) [Infinite α] : ℕ → α
  | n =>
    letI := Classical.decEq α
    Classical.choose
      (exists_not_mem_finset
        ((Multiset.range n).pmap (fun m (hm : m < n) => nat_embedding_aux m) fun _ =>
            Multiset.mem_range.1).toFinset)
#align infinite.nat_embedding_aux infinite.nat_embedding_aux

private theorem nat_embedding_aux_injective (α : Type _) [Infinite α] :
    Function.Injective (natEmbeddingAux α) :=
  by
  rintro m n h
  letI := Classical.decEq α
  wlog hmlen : m ≤ n generalizing m n
  · exact (this h.symm <| le_of_not_le hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine'
    (Classical.choose_spec
        (exists_not_mem_finset
          ((Multiset.range n).pmap (fun m (hm : m < n) => nat_embedding_aux α m) fun _ =>
              Multiset.mem_range.1).toFinset))
      _
  refine' Multiset.mem_toFinset.2 (Multiset.mem_pmap.2 ⟨m, Multiset.mem_range.2 hmn, _⟩)
  rw [h, nat_embedding_aux]
#align infinite.nat_embedding_aux_injective infinite.nat_embedding_aux_injective

#print Infinite.natEmbedding /-
/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def natEmbedding (α : Type _) [Infinite α] : ℕ ↪ α :=
  ⟨_, natEmbeddingAux_injective α⟩
#align infinite.nat_embedding Infinite.natEmbedding
-/

#print Infinite.exists_subset_card_eq /-
/-- See `infinite.exists_superset_card_eq` for a version that, for a `s : finset α`,
provides a superset `t : finset α`, `s ⊆ t` such that `t.card` is fixed. -/
theorem exists_subset_card_eq (α : Type _) [Infinite α] (n : ℕ) : ∃ s : Finset α, s.card = n :=
  ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩
#align infinite.exists_subset_card_eq Infinite.exists_subset_card_eq
-/

#print Infinite.exists_superset_card_eq /-
/-- See `infinite.exists_subset_card_eq` for a version that provides an arbitrary
`s : finset α` for any cardinality. -/
theorem exists_superset_card_eq [Infinite α] (s : Finset α) (n : ℕ) (hn : s.card ≤ n) :
    ∃ t : Finset α, s ⊆ t ∧ t.card = n :=
  by
  induction' n with n IH generalizing s
  · exact ⟨s, subset_refl _, Nat.eq_zero_of_le_zero hn⟩
  · cases' hn.eq_or_lt with hn' hn'
    · exact ⟨s, subset_refl _, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_not_mem_finset t
    refine' ⟨Finset.cons x t hx, hs.trans (Finset.subset_cons _), _⟩
    simp [hx, ht]
#align infinite.exists_superset_card_eq Infinite.exists_superset_card_eq
-/

end Infinite

#print fintypeOfFinsetCardLe /-
/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintypeOfFinsetCardLe {ι : Type _} (n : ℕ) (w : ∀ s : Finset ι, s.card ≤ n) :
    Fintype ι := by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w
#align fintype_of_finset_card_le fintypeOfFinsetCardLe
-/

/- warning: not_injective_infinite_finite -> not_injective_infinite_finite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Infinite.{u1} α] [_inst_2 : Finite.{u2} β] (f : α -> β), Not (Function.Injective.{u1, u2} α β f)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Infinite.{u2} α] [_inst_2 : Finite.{u1} β] (f : α -> β), Not (Function.Injective.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align not_injective_infinite_finite not_injective_infinite_finiteₓ'. -/
theorem not_injective_infinite_finite {α β} [Infinite α] [Finite β] (f : α → β) : ¬Injective f :=
  fun hf => (Finite.of_injective f hf).False
#align not_injective_infinite_finite not_injective_infinite_finite

/- warning: finite.exists_ne_map_eq_of_infinite -> Finite.exists_ne_map_eq_of_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Infinite.{u1} α] [_inst_2 : Finite.{u2} β] (f : α -> β), Exists.{u1} α (fun (x : α) => Exists.{u1} α (fun (y : α) => And (Ne.{u1} α x y) (Eq.{u2} β (f x) (f y))))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Infinite.{u2} α] [_inst_2 : Finite.{u1} β] (f : α -> β), Exists.{u2} α (fun (x : α) => Exists.{u2} α (fun (y : α) => And (Ne.{u2} α x y) (Eq.{u1} β (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align finite.exists_ne_map_eq_of_infinite Finite.exists_ne_map_eq_of_infiniteₓ'. -/
/-- The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `finite.exists_infinite_fiber`.
-/
theorem Finite.exists_ne_map_eq_of_infinite {α β} [Infinite α] [Finite β] (f : α → β) :
    ∃ x y : α, x ≠ y ∧ f x = f y := by
  simpa only [injective, not_forall, not_imp, and_comm] using not_injective_infinite_finite f
#align finite.exists_ne_map_eq_of_infinite Finite.exists_ne_map_eq_of_infinite

/- warning: function.embedding.is_empty -> Function.Embedding.is_empty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Infinite.{u1} α] [_inst_2 : Finite.{u2} β], IsEmpty.{max 1 (imax u1 u2)} (Function.Embedding.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Infinite.{u1} α] [_inst_2 : Finite.{u2} β], IsEmpty.{max (max 1 u2) u1} (Function.Embedding.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align function.embedding.is_empty Function.Embedding.is_emptyₓ'. -/
instance Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β) :=
  ⟨fun f => not_injective_infinite_finite f f.2⟩
#align function.embedding.is_empty Function.Embedding.is_empty

/- warning: finite.exists_infinite_fiber -> Finite.exists_infinite_fiber is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Finite.{succ u2} β] (f : α -> β), Exists.{succ u2} β (fun (y : β) => Infinite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u2} α] [_inst_2 : Finite.{succ u1} β] (f : α -> β), Exists.{succ u1} β (fun (y : β) => Infinite.{succ u2} (Set.Elem.{u2} α (Set.preimage.{u2, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y))))
Case conversion may be inaccurate. Consider using '#align finite.exists_infinite_fiber Finite.exists_infinite_fiberₓ'. -/
/-- The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `finite.exists_ne_map_eq_of_infinite`
-/
theorem Finite.exists_infinite_fiber [Infinite α] [Finite β] (f : α → β) :
    ∃ y : β, Infinite (f ⁻¹' {y}) := by
  classical
    by_contra' hf
    cases nonempty_fintype β
    haveI := fun y => fintypeOfNotInfinite <| hf y
    let key : Fintype α :=
      { elems := univ.bUnion fun y : β => (f ⁻¹' {y}).toFinset
        complete := by simp }
    exact key.false
#align finite.exists_infinite_fiber Finite.exists_infinite_fiber

/- warning: not_surjective_finite_infinite -> not_surjective_finite_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u1} α] [_inst_2 : Infinite.{u2} β] (f : α -> β), Not (Function.Surjective.{u1, u2} α β f)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Finite.{u2} α] [_inst_2 : Infinite.{u1} β] (f : α -> β), Not (Function.Surjective.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align not_surjective_finite_infinite not_surjective_finite_infiniteₓ'. -/
theorem not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α → β) : ¬Surjective f :=
  fun hf => (Infinite.of_surjective f hf).not_finite ‹_›
#align not_surjective_finite_infinite not_surjective_finite_infinite

section Trunc

#print truncOfCardPos /-
/-- A `fintype` with positive cardinality constructively contains an element.
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α :=
  letI := fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α
#align trunc_of_card_pos truncOfCardPos
-/

end Trunc

#print Fintype.induction_subsingleton_or_nontrivial /-
/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `fintype.card`).

The major premise is `fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_elim]
theorem Fintype.induction_subsingleton_or_nontrivial {P : ∀ (α) [Fintype α], Prop} (α : Type _)
    [Fintype α] (hbase : ∀ (α) [Fintype α] [Subsingleton α], P α)
    (hstep :
      ∀ (α) [Fintype α] [Nontrivial α],
        ∀ ih : ∀ (β) [Fintype β], ∀ h : Fintype.card β < Fintype.card α, P β, P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction' n using Nat.strong_induction_on with n ih generalizing α
  cases' subsingleton_or_nontrivial α with hsing hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.card β) hlt _ rfl
#align fintype.induction_subsingleton_or_nontrivial Fintype.induction_subsingleton_or_nontrivial
-/

namespace Tactic

open Positivity

private theorem card_univ_pos (α : Type _) [Fintype α] [Nonempty α] :
    0 < (Finset.univ : Finset α).card :=
  Finset.univ_nonempty.card_pos
#align tactic.card_univ_pos tactic.card_univ_pos

/-- Extension for the `positivity` tactic: `finset.card s` is positive if `s` is nonempty. -/
@[positivity]
unsafe def positivity_finset_card : expr → tactic strictness
  | q(Finset.card $(s)) => do
    let p
      ←-- TODO: Partial decision procedure for `finset.nonempty`
            to_expr
            ``(Finset.Nonempty $(s)) >>=
          find_assumption
    positive <$> mk_app `` Finset.Nonempty.card_pos [p]
  | q(@Fintype.card $(α) $(i)) => positive <$> mk_mapp `` Fintype.card_pos [α, i, none]
  | e =>
    pp e >>=
      fail ∘
        format.bracket "The expression `" "` isn't of the form `finset.card s` or `fintype.card α`"
#align tactic.positivity_finset_card tactic.positivity_finset_card

end Tactic

