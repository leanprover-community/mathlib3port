/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module logic.equiv.list
! leanprover-community/mathlib commit d11893b411025250c8e61ff2f12ccbd7ee35ab15
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Data.Vector.Basic
import Mathbin.Logic.Denumerable

/-!
# Equivalences involving `list`-like types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines some additional constructive equivalences using `encodable` and the pairing
function on `ℕ`.
-/


open Nat List

namespace Encodable

variable {α : Type _}

section List

variable [Encodable α]

#print Encodable.encodeList /-
/-- Explicit encoding function for `list α` -/
def encodeList : List α → ℕ
  | [] => 0
  | a :: l => succ (pair (encode a) (encode_list l))
#align encodable.encode_list Encodable.encodeList
-/

#print Encodable.decodeList /-
/-- Explicit decoding function for `list α` -/
def decodeList : ℕ → Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
      (· :: ·) <$> decode α v₁ <*> decode_list v₂
#align encodable.decode_list Encodable.decodeList
-/

#print List.encodable /-
/-- If `α` is encodable, then so is `list α`. This uses the `mkpair` and `unpair` functions from
`data.nat.pairing`. -/
instance List.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, fun l => by
    induction' l with a l IH <;> simp [encode_list, decode_list, unpair_mkpair, encodek, *]⟩
#align list.encodable List.encodable
-/

#print List.countable /-
instance List.countable {α : Type _} [Countable α] : Countable (List α) :=
  by
  haveI := Encodable.ofCountable α
  infer_instance
#align list.countable List.countable
-/

#print Encodable.encode_list_nil /-
@[simp]
theorem encode_list_nil : encode (@nil α) = 0 :=
  rfl
#align encodable.encode_list_nil Encodable.encode_list_nil
-/

#print Encodable.encode_list_cons /-
@[simp]
theorem encode_list_cons (a : α) (l : List α) :
    encode (a :: l) = succ (pair (encode a) (encode l)) :=
  rfl
#align encodable.encode_list_cons Encodable.encode_list_cons
-/

#print Encodable.decode_list_zero /-
@[simp]
theorem decode_list_zero : decode (List α) 0 = some [] :=
  show decodeList 0 = some [] by rw [decode_list]
#align encodable.decode_list_zero Encodable.decode_list_zero
-/

/- warning: encodable.decode_list_succ -> Encodable.decode_list_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Encodable.{u1} α] (v : Nat), Eq.{succ u1} (Option.{u1} (List.{u1} α)) (Encodable.decode.{u1} (List.{u1} α) (List.encodable.{u1} α _inst_1) (Nat.succ v)) (Seq.seq.{u1, u1} Option.{u1} (Applicative.toHasSeq.{u1, u1} Option.{u1} (Monad.toApplicative.{u1, u1} Option.{u1} Option.monad.{u1})) (List.{u1} α) (List.{u1} α) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α ((List.{u1} α) -> (List.{u1} α)) (fun (_x : α) (_y : List.{u1} α) => List.cons.{u1} α _x _y) (Encodable.decode.{u1} α _inst_1 (Prod.fst.{0, 0} Nat Nat (Nat.unpair v)))) (Encodable.decode.{u1} (List.{u1} α) (List.encodable.{u1} α _inst_1) (Prod.snd.{0, 0} Nat Nat (Nat.unpair v))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Encodable.{u1} α] (v : Nat), Eq.{succ u1} (Option.{u1} (List.{u1} α)) (Encodable.decode.{u1} (List.{u1} α) (List.encodable.{u1} α _inst_1) (Nat.succ v)) (Seq.seq.{u1, u1} Option.{u1} (Applicative.toSeq.{u1, u1} Option.{u1} (Alternative.toApplicative.{u1, u1} Option.{u1} instAlternativeOption.{u1})) (List.{u1} α) (List.{u1} α) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α ((List.{u1} α) -> (List.{u1} α)) (fun (_x : α) (_y : List.{u1} α) => List.cons.{u1} α _x _y) (Encodable.decode.{u1} α _inst_1 (Prod.fst.{0, 0} Nat Nat (Nat.unpair v)))) (fun (x._@.Mathlib.Logic.Equiv.List._hyg.562 : Unit) => Encodable.decode.{u1} (List.{u1} α) (List.encodable.{u1} α _inst_1) (Prod.snd.{0, 0} Nat Nat (Nat.unpair v))))
Case conversion may be inaccurate. Consider using '#align encodable.decode_list_succ Encodable.decode_list_succₓ'. -/
@[simp]
theorem decode_list_succ (v : ℕ) :
    decode (List α) (succ v) = (· :: ·) <$> decode α v.unpair.1 <*> decode (List α) v.unpair.2 :=
  show decodeList (succ v) = _ by
    cases' e : unpair v with v₁ v₂
    simp [decode_list, e]; rfl
#align encodable.decode_list_succ Encodable.decode_list_succ

#print Encodable.length_le_encode /-
theorem length_le_encode : ∀ l : List α, length l ≤ encode l
  | [] => zero_le _
  | a :: l => succ_le_succ <| (length_le_encode l).trans (right_le_pair _ _)
#align encodable.length_le_encode Encodable.length_le_encode
-/

end List

section Finset

variable [Encodable α]

private def enle : α → α → Prop :=
  encode ⁻¹'o (· ≤ ·)

private theorem enle.is_linear_order : IsLinearOrder α Enle :=
  (RelEmbedding.preimage ⟨encode, encode_injective⟩ (· ≤ ·)).IsLinearOrder

private def decidable_enle (a b : α) : Decidable (Enle a b) := by
  unfold enle Order.Preimage <;> infer_instance

attribute [local instance] enle.is_linear_order decidable_enle

#print Encodable.encodeMultiset /-
/-- Explicit encoding function for `multiset α` -/
def encodeMultiset (s : Multiset α) : ℕ :=
  encode (s.sort Enle)
#align encodable.encode_multiset Encodable.encodeMultiset
-/

#print Encodable.decodeMultiset /-
/-- Explicit decoding function for `multiset α` -/
def decodeMultiset (n : ℕ) : Option (Multiset α) :=
  coe <$> decode (List α) n
#align encodable.decode_multiset Encodable.decodeMultiset
-/

#print Multiset.encodable /-
/-- If `α` is encodable, then so is `multiset α`. -/
instance Multiset.encodable : Encodable (Multiset α) :=
  ⟨encodeMultiset, decodeMultiset, fun s => by simp [encode_multiset, decode_multiset, encodek]⟩
#align multiset.encodable Multiset.encodable
-/

#print Multiset.countable /-
/-- If `α` is countable, then so is `multiset α`. -/
instance Multiset.countable {α : Type _} [Countable α] : Countable (Multiset α) :=
  Quotient.countable
#align multiset.countable Multiset.countable
-/

end Finset

#print Encodable.encodableOfList /-
/-- A listable type with decidable equality is encodable. -/
def encodableOfList [DecidableEq α] (l : List α) (H : ∀ x, x ∈ l) : Encodable α :=
  ⟨fun a => indexOf a l, l.get?, fun a => indexOf_get? (H _)⟩
#align encodable.encodable_of_list Encodable.encodableOfList
-/

#print Fintype.truncEncodable /-
/-- A finite type is encodable. Because the encoding is not unique, we wrap it in `trunc` to
preserve computability. -/
def Fintype.truncEncodable (α : Type _) [DecidableEq α] [Fintype α] : Trunc (Encodable α) :=
  @Quot.recOnSubsingleton' _ (fun s : Multiset α => (∀ x : α, x ∈ s) → Trunc (Encodable α)) _
    Finset.univ.1 (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ
#align fintype.trunc_encodable Fintype.truncEncodable
-/

#print Fintype.toEncodable /-
/-- A noncomputable way to arbitrarily choose an ordering on a finite type.
It is not made into a global instance, since it involves an arbitrary choice.
This can be locally made into an instance with `local attribute [instance] fintype.to_encodable`. -/
noncomputable def Fintype.toEncodable (α : Type _) [Fintype α] : Encodable α := by
  classical exact (Fintype.truncEncodable α).out
#align fintype.to_encodable Fintype.toEncodable
-/

#print Vector.encodable /-
/-- If `α` is encodable, then so is `vector α n`. -/
instance Vector.encodable [Encodable α] {n} : Encodable (Vector α n) :=
  Subtype.encodable
#align vector.encodable Vector.encodable
-/

#print Vector.countable /-
/-- If `α` is countable, then so is `vector α n`. -/
instance Vector.countable [Countable α] {n} : Countable (Vector α n) :=
  Subtype.countable
#align vector.countable Vector.countable
-/

#print Encodable.finArrow /-
/-- If `α` is encodable, then so is `fin n → α`. -/
instance finArrow [Encodable α] {n} : Encodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align encodable.fin_arrow Encodable.finArrow
-/

#print Encodable.finPi /-
instance finPi (n) (π : Fin n → Type _) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)
#align encodable.fin_pi Encodable.finPi
-/

#print Finset.encodable /-
/-- If `α` is encodable, then so is `finset α`. -/
instance Finset.encodable [Encodable α] : Encodable (Finset α) :=
  haveI := decidable_eq_of_encodable α
  of_equiv { s : Multiset α // s.Nodup }
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩
#align finset.encodable Finset.encodable
-/

#print Finset.countable /-
/-- If `α` is countable, then so is `finset α`. -/
instance Finset.countable [Countable α] : Countable (Finset α) :=
  Finset.val_injective.Countable
#align finset.countable Finset.countable
-/

#print Encodable.fintypeArrow /-
-- TODO: Unify with `fintype_pi` and find a better name
/-- When `α` is finite and `β` is encodable, `α → β` is encodable too. Because the encoding is not
unique, we wrap it in `trunc` to preserve computability. -/
def fintypeArrow (α : Type _) (β : Type _) [DecidableEq α] [Fintype α] [Encodable β] :
    Trunc (Encodable (α → β)) :=
  (Fintype.truncEquivFin α).map fun f =>
    Encodable.ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr f (Equiv.refl _)
#align encodable.fintype_arrow Encodable.fintypeArrow
-/

#print Encodable.fintypePi /-
/-- When `α` is finite and all `π a` are encodable, `Π a, π a` is encodable too. Because the
encoding is not unique, we wrap it in `trunc` to preserve computability. -/
def fintypePi (α : Type _) (π : α → Type _) [DecidableEq α] [Fintype α] [∀ a, Encodable (π a)] :
    Trunc (Encodable (∀ a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σa, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
      Trunc.mk <|
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _) (Equiv.piEquivSubtypeSigma α π)
#align encodable.fintype_pi Encodable.fintypePi
-/

#print Encodable.sortedUniv /-
/-- The elements of a `fintype` as a sorted list. -/
def sortedUniv (α) [Fintype α] [Encodable α] : List α :=
  Finset.univ.sort (Encodable.encode' α ⁻¹'o (· ≤ ·))
#align encodable.sorted_univ Encodable.sortedUniv
-/

#print Encodable.mem_sortedUniv /-
@[simp]
theorem mem_sortedUniv {α} [Fintype α] [Encodable α] (x : α) : x ∈ sortedUniv α :=
  (Finset.mem_sort _).2 (Finset.mem_univ _)
#align encodable.mem_sorted_univ Encodable.mem_sortedUniv
-/

#print Encodable.length_sortedUniv /-
@[simp]
theorem length_sortedUniv (α) [Fintype α] [Encodable α] : (sortedUniv α).length = Fintype.card α :=
  Finset.length_sort _
#align encodable.length_sorted_univ Encodable.length_sortedUniv
-/

#print Encodable.sortedUniv_nodup /-
@[simp]
theorem sortedUniv_nodup (α) [Fintype α] [Encodable α] : (sortedUniv α).Nodup :=
  Finset.sort_nodup _ _
#align encodable.sorted_univ_nodup Encodable.sortedUniv_nodup
-/

#print Encodable.sortedUniv_toFinset /-
@[simp]
theorem sortedUniv_toFinset (α) [Fintype α] [Encodable α] [DecidableEq α] :
    (sortedUniv α).toFinset = Finset.univ :=
  Finset.sort_toFinset _ _
#align encodable.sorted_univ_to_finset Encodable.sortedUniv_toFinset
-/

#print Encodable.fintypeEquivFin /-
/-- An encodable `fintype` is equivalent to the same size `fin`. -/
def fintypeEquivFin {α} [Fintype α] [Encodable α] : α ≃ Fin (Fintype.card α) :=
  by
  haveI : DecidableEq α := Encodable.decidableEqOfEncodable _
  trans
  · exact ((sorted_univ_nodup α).getEquivOfForallMemList _ mem_sorted_univ).symm
  exact Equiv.cast (congr_arg _ (length_sorted_univ α))
#align encodable.fintype_equiv_fin Encodable.fintypeEquivFin
-/

#print Encodable.fintypeArrowOfEncodable /-
/-- If `α` and `β` are encodable and `α` is a fintype, then `α → β` is encodable as well. -/
instance fintypeArrowOfEncodable {α β : Type _} [Encodable α] [Fintype α] [Encodable β] :
    Encodable (α → β) :=
  ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)
#align encodable.fintype_arrow_of_encodable Encodable.fintypeArrowOfEncodable
-/

end Encodable

namespace Denumerable

variable {α : Type _} {β : Type _} [Denumerable α] [Denumerable β]

open Encodable

section List

/- warning: denumerable.denumerable_list_aux -> Denumerable.denumerable_list_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Denumerable.{u1} α] (n : Nat), Exists.{succ u1} (List.{u1} α) (fun (a : List.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (List.{u1} α) (Option.{u1} (List.{u1} α)) (Option.hasMem.{u1} (List.{u1} α)) a (Encodable.decodeList.{u1} α (Denumerable.toEncodable.{u1} α _inst_1) n)) (fun (H : Membership.Mem.{u1, u1} (List.{u1} α) (Option.{u1} (List.{u1} α)) (Option.hasMem.{u1} (List.{u1} α)) a (Encodable.decodeList.{u1} α (Denumerable.toEncodable.{u1} α _inst_1) n)) => Eq.{1} Nat (Encodable.encodeList.{u1} α (Denumerable.toEncodable.{u1} α _inst_1) a) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Denumerable.{u1} α] (n : Nat), Exists.{succ u1} (List.{u1} α) (fun (a : List.{u1} α) => And (Membership.mem.{u1, u1} (List.{u1} α) (Option.{u1} (List.{u1} α)) (Option.instMembershipOption.{u1} (List.{u1} α)) a (Encodable.decodeList.{u1} α (Denumerable.toEncodable.{u1} α _inst_1) n)) (Eq.{1} Nat (Encodable.encodeList.{u1} α (Denumerable.toEncodable.{u1} α _inst_1) a) n))
Case conversion may be inaccurate. Consider using '#align denumerable.denumerable_list_aux Denumerable.denumerable_list_auxₓ'. -/
theorem denumerable_list_aux : ∀ n : ℕ, ∃ a ∈ @decodeList α _ n, encodeList a = n
  | 0 => by rw [decode_list] <;> exact ⟨_, rfl, rfl⟩
  | succ v => by
    cases' e : unpair v with v₁ v₂
    have h := unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use of_nat α v₁ :: a
    simp [decode_list, e, h₂, h₁, encode_list, mkpair_unpair' e]
#align denumerable.denumerable_list_aux Denumerable.denumerable_list_aux

#print Denumerable.denumerableList /-
/-- If `α` is denumerable, then so is `list α`. -/
instance denumerableList : Denumerable (List α) :=
  ⟨denumerable_list_aux⟩
#align denumerable.denumerable_list Denumerable.denumerableList
-/

#print Denumerable.list_ofNat_zero /-
@[simp]
theorem list_ofNat_zero : ofNat (List α) 0 = [] := by rw [← @encode_list_nil α, of_nat_encode]
#align denumerable.list_of_nat_zero Denumerable.list_ofNat_zero
-/

#print Denumerable.list_ofNat_succ /-
@[simp]
theorem list_ofNat_succ (v : ℕ) :
    ofNat (List α) (succ v) = ofNat α v.unpair.1 :: ofNat (List α) v.unpair.2 :=
  ofNat_of_decode <|
    show decodeList (succ v) = _ by
      cases' e : unpair v with v₁ v₂
      simp [decode_list, e]
      rw [show decode_list v₂ = decode (List α) v₂ from rfl, decode_eq_of_nat] <;> rfl
#align denumerable.list_of_nat_succ Denumerable.list_ofNat_succ
-/

end List

section Multiset

#print Denumerable.lower /-
/-- Outputs the list of differences of the input list, that is
`lower [a₁, a₂, ...] n = [a₁ - n, a₂ - a₁, ...]` -/
def lower : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m - n) :: lower l m
#align denumerable.lower Denumerable.lower
-/

#print Denumerable.raise /-
/-- Outputs the list of partial sums of the input list, that is
`raise [a₁, a₂, ...] n = [n + a₁, n + a₁ + a₂, ...]` -/
def raise : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m + n) :: raise l (m + n)
#align denumerable.raise Denumerable.raise
-/

#print Denumerable.lower_raise /-
theorem lower_raise : ∀ l n, lower (raise l n) n = l
  | [], n => rfl
  | m :: l, n => by rw [raise, lower, add_tsub_cancel_right, lower_raise]
#align denumerable.lower_raise Denumerable.lower_raise
-/

#print Denumerable.raise_lower /-
theorem raise_lower : ∀ {l n}, List.Sorted (· ≤ ·) (n :: l) → raise (lower l n) n = l
  | [], n, h => rfl
  | m :: l, n, h =>
    by
    have : n ≤ m := List.rel_of_sorted_cons h _ (l.mem_cons_self _)
    simp [raise, lower, tsub_add_cancel_of_le this, raise_lower h.of_cons]
#align denumerable.raise_lower Denumerable.raise_lower
-/

#print Denumerable.raise_chain /-
theorem raise_chain : ∀ l n, List.Chain (· ≤ ·) n (raise l n)
  | [], n => List.Chain.nil
  | m :: l, n => List.Chain.cons (Nat.le_add_left _ _) (raise_chain _ _)
#align denumerable.raise_chain Denumerable.raise_chain
-/

#print Denumerable.raise_sorted /-
/-- `raise l n` is an non-decreasing sequence. -/
theorem raise_sorted : ∀ l n, List.Sorted (· ≤ ·) (raise l n)
  | [], n => List.sorted_nil
  | m :: l, n => List.chain_iff_pairwise.1 (raise_chain _ _)
#align denumerable.raise_sorted Denumerable.raise_sorted
-/

#print Denumerable.multiset /-
/-- If `α` is denumerable, then so is `multiset α`. Warning: this is *not* the same encoding as used
in `multiset.encodable`. -/
instance multiset : Denumerable (Multiset α) :=
  mk'
    ⟨fun s : Multiset α => encode <| lower ((s.map encode).sort (· ≤ ·)) 0, fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List ℕ) n) 0), fun s => by
      have :=
          raise_lower (List.sorted_cons.2 ⟨fun n _ => zero_le n, (s.map encode).sort_sorted _⟩) <;>
        simp [-Multiset.coe_map, this],
      fun n => by
      simp [-Multiset.coe_map, List.mergeSort_eq_self _ (raise_sorted _ _), lower_raise]⟩
#align denumerable.multiset Denumerable.multiset
-/

end Multiset

section Finset

#print Denumerable.lower' /-
/-- Outputs the list of differences minus one of the input list, that is
`lower' [a₁, a₂, a₃, ...] n = [a₁ - n, a₂ - a₁ - 1, a₃ - a₂ - 1, ...]`. -/
def lower' : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m - n) :: lower' l (m + 1)
#align denumerable.lower' Denumerable.lower'
-/

#print Denumerable.raise' /-
/-- Outputs the list of partial sums plus one of the input list, that is
`raise [a₁, a₂, a₃, ...] n = [n + a₁, n + a₁ + a₂ + 1, n + a₁ + a₂ + a₃ + 2, ...]`. Adding one each
time ensures the elements are distinct. -/
def raise' : List ℕ → ℕ → List ℕ
  | [], n => []
  | m :: l, n => (m + n) :: raise' l (m + n + 1)
#align denumerable.raise' Denumerable.raise'
-/

#print Denumerable.lower_raise' /-
theorem lower_raise' : ∀ l n, lower' (raise' l n) n = l
  | [], n => rfl
  | m :: l, n => by simp [raise', lower', add_tsub_cancel_right, lower_raise']
#align denumerable.lower_raise' Denumerable.lower_raise'
-/

#print Denumerable.raise_lower' /-
theorem raise_lower' : ∀ {l n}, (∀ m ∈ l, n ≤ m) → List.Sorted (· < ·) l → raise' (lower' l n) n = l
  | [], n, h₁, h₂ => rfl
  | m :: l, n, h₁, h₂ => by
    have : n ≤ m := h₁ _ (l.mem_cons_self _)
    simp [raise', lower', tsub_add_cancel_of_le this,
      raise_lower' (List.rel_of_sorted_cons h₂ : ∀ a ∈ l, m < a) h₂.of_cons]
#align denumerable.raise_lower' Denumerable.raise_lower'
-/

#print Denumerable.raise'_chain /-
theorem raise'_chain : ∀ (l) {m n}, m < n → List.Chain (· < ·) m (raise' l n)
  | [], m, n, h => List.Chain.nil
  | a :: l, m, n, h =>
    List.Chain.cons (lt_of_lt_of_le h (Nat.le_add_left _ _)) (raise'_chain _ (lt_succ_self _))
#align denumerable.raise'_chain Denumerable.raise'_chain
-/

#print Denumerable.raise'_sorted /-
/-- `raise' l n` is a strictly increasing sequence. -/
theorem raise'_sorted : ∀ l n, List.Sorted (· < ·) (raise' l n)
  | [], n => List.sorted_nil
  | m :: l, n => List.chain_iff_pairwise.1 (raise'_chain _ (lt_succ_self _))
#align denumerable.raise'_sorted Denumerable.raise'_sorted
-/

#print Denumerable.raise'Finset /-
/-- Makes `raise' l n` into a finset. Elements are distinct thanks to `raise'_sorted`. -/
def raise'Finset (l : List ℕ) (n : ℕ) : Finset ℕ :=
  ⟨raise' l n, (raise'_sorted _ _).imp (@ne_of_lt _ _)⟩
#align denumerable.raise'_finset Denumerable.raise'Finset
-/

#print Denumerable.finset /-
/-- If `α` is denumerable, then so is `finset α`. Warning: this is *not* the same encoding as used
in `finset.encodable`. -/
instance finset : Denumerable (Finset α) :=
  mk'
    ⟨fun s : Finset α => encode <| lower' ((s.map (eqv α).toEmbedding).sort (· ≤ ·)) 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List ℕ) n) 0), fun s =>
      Finset.eq_of_veq <| by
        simp [-Multiset.coe_map, raise'_finset,
          raise_lower' (fun n _ => zero_le n) (Finset.sort_sorted_lt _)],
      fun n => by
      simp [-Multiset.coe_map, Finset.map, raise'_finset, Finset.sort,
        List.mergeSort_eq_self (· ≤ ·) ((raise'_sorted _ _).imp (@le_of_lt _ _)), lower_raise']⟩
#align denumerable.finset Denumerable.finset
-/

end Finset

end Denumerable

namespace Equiv

#print Equiv.listUnitEquiv /-
/-- The type lists on unit is canonically equivalent to the natural numbers. -/
def listUnitEquiv : List Unit ≃ ℕ where
  toFun := List.length
  invFun n := List.replicate n ()
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate n ()
#align equiv.list_unit_equiv Equiv.listUnitEquiv
-/

#print Equiv.listNatEquivNat /-
/-- `list ℕ` is equivalent to `ℕ`. -/
def listNatEquivNat : List ℕ ≃ ℕ :=
  Denumerable.eqv _
#align equiv.list_nat_equiv_nat Equiv.listNatEquivNat
-/

#print Equiv.listEquivSelfOfEquivNat /-
/-- If `α` is equivalent to `ℕ`, then `list α` is equivalent to `α`. -/
def listEquivSelfOfEquivNat {α : Type _} (e : α ≃ ℕ) : List α ≃ α :=
  calc
    List α ≃ List ℕ := listEquivOfEquiv e
    _ ≃ ℕ := listNatEquivNat
    _ ≃ α := e.symm
    
#align equiv.list_equiv_self_of_equiv_nat Equiv.listEquivSelfOfEquivNat
-/

end Equiv

