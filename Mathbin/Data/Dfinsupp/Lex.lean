/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
import Data.Dfinsupp.Order
import Data.Dfinsupp.NeLocus
import Order.WellFoundedSet

#align_import data.dfinsupp.lex from "leanprover-community/mathlib"@"34ee86e6a59d911a8e4f89b68793ee7577ae79c7"

/-!
# Lexicographic order on finitely supported dependent functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lexicographic order on `dfinsupp`.
-/


variable {ι : Type _} {α : ι → Type _}

namespace DFinsupp

section Zero

variable [∀ i, Zero (α i)]

#print DFinsupp.Lex /-
/-- `dfinsupp.lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.
The type synonym `lex (Π₀ i, α i)` has an order given by `dfinsupp.lex (<) (λ i, (<))`.
-/
protected def Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
  Pi.Lex r s x y
#align dfinsupp.lex DFinsupp.Lex
-/

#print Pi.lex_eq_dfinsupp_lex /-
theorem Pi.lex_eq_dfinsupp_lex {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop} (a b : Π₀ i, α i) :
    Pi.Lex r s (a : ∀ i, α i) b = DFinsupp.Lex r s a b :=
  rfl
#align pi.lex_eq_dfinsupp_lex Pi.lex_eq_dfinsupp_lex
-/

#print DFinsupp.lex_def /-
theorem lex_def {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop} {a b : Π₀ i, α i} :
    DFinsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s j (a j) (b j) :=
  Iff.rfl
#align dfinsupp.lex_def DFinsupp.lex_def
-/

instance [LT ι] [∀ i, LT (α i)] : LT (Lex (Π₀ i, α i)) :=
  ⟨fun f g => DFinsupp.Lex (· < ·) (fun i => (· < ·)) (ofLex f) (ofLex g)⟩

#print DFinsupp.lex_lt_of_lt_of_preorder /-
theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  by
  obtain ⟨hle, j, hlt⟩ := Pi.lt_def.1 hlt
  classical
#align dfinsupp.lex_lt_of_lt_of_preorder DFinsupp.lex_lt_of_lt_of_preorder
-/

#print DFinsupp.lex_lt_of_lt /-
theorem lex_lt_of_lt [∀ i, PartialOrder (α i)] (r) [IsStrictOrder ι r] {x y : Π₀ i, α i}
    (hlt : x < y) : Pi.Lex r (fun i => (· < ·)) x y := by simp_rw [Pi.Lex, le_antisymm_iff];
  exact lex_lt_of_lt_of_preorder r hlt
#align dfinsupp.lex_lt_of_lt DFinsupp.lex_lt_of_lt
-/

#print DFinsupp.Lex.isStrictOrder /-
instance Lex.isStrictOrder [LinearOrder ι] [∀ i, PartialOrder (α i)] :
    IsStrictOrder (Lex (Π₀ i, α i)) (· < ·) :=
  let i : IsStrictOrder (Lex (∀ i, α i)) (· < ·) := Pi.Lex.isStrictOrder
  { irrefl := toLex.Surjective.forall.2 fun a => @irrefl _ _ i.to_isIrrefl a
    trans := toLex.Surjective.forall₃.2 fun a b c => @trans _ _ i.to_isTrans a b c }
#align dfinsupp.lex.is_strict_order DFinsupp.Lex.isStrictOrder
-/

variable [LinearOrder ι]

#print DFinsupp.Lex.partialOrder /-
/-- The partial order on `dfinsupp`s obtained by the lexicographic ordering.
See `dfinsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [∀ i, PartialOrder (α i)] : PartialOrder (Lex (Π₀ i, α i)) :=
  PartialOrder.lift (fun x => toLex ⇑(ofLex x)) DFinsupp.coeFn_injective
#align dfinsupp.lex.partial_order DFinsupp.Lex.partialOrder
-/

section LinearOrder

variable [∀ i, LinearOrder (α i)]

/-- Auxiliary helper to case split computably. There is no need for this to be public, as it
can be written with `or.by_cases` on `lt_trichotomy` once the instances below are constructed. -/
private def lt_trichotomy_rec {P : Lex (Π₀ i, α i) → Lex (Π₀ i, α i) → Sort _}
    (h_lt : ∀ {f g}, toLex f < toLex g → P (toLex f) (toLex g))
    (h_eq : ∀ {f g}, toLex f = toLex g → P (toLex f) (toLex g))
    (h_gt : ∀ {f g}, toLex g < toLex f → P (toLex f) (toLex g)) : ∀ f g, P f g :=
  Lex.rec fun f =>
    Lex.rec fun g =>
      match (motive := ∀ y, (f.neLocus g).min = y → _) _, rfl with
      | ⊤, h => h_eq (neLocus_eq_empty.mp <| Finset.min_eq_top.mp h)
      | (wit : ι), h =>
        (mem_neLocus.mp <| Finset.mem_of_min h).lt_or_lt.byCases
          (fun hwit =>
            h_lt ⟨wit, fun j hj => not_mem_neLocus.mp (Finset.not_mem_of_lt_min hj h), hwit⟩)
          fun hwit =>
          h_gt
            ⟨wit, fun j hj =>
              not_mem_neLocus.mp (Finset.not_mem_of_lt_min hj <| by rwa [ne_locus_comm]), hwit⟩

/- ./././Mathport/Syntax/Translate/Command.lean:332:38: unsupported irreducible non-definition -/
#print DFinsupp.Lex.decidableLE /-
irreducible_def Lex.decidableLE : @DecidableRel (Lex (Π₀ i, α i)) (· ≤ ·) :=
  ltTrichotomyRec (fun f g h => isTrue <| Or.inr h) (fun f g h => isTrue <| Or.inl <| congr_arg _ h)
    fun f g h => isFalse fun h' => (lt_irrefl _ (h.trans_le h')).elim
#align dfinsupp.lex.decidable_le DFinsupp.Lex.decidableLE
-/

/- ./././Mathport/Syntax/Translate/Command.lean:332:38: unsupported irreducible non-definition -/
#print DFinsupp.Lex.decidableLT /-
irreducible_def Lex.decidableLT : @DecidableRel (Lex (Π₀ i, α i)) (· < ·) :=
  ltTrichotomyRec (fun f g h => isTrue h) (fun f g h => isFalse h.not_lt) fun f g h =>
    isFalse h.asymm
#align dfinsupp.lex.decidable_lt DFinsupp.Lex.decidableLT
-/

#print DFinsupp.Lex.linearOrder /-
/-- The linear order on `dfinsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder : LinearOrder (Lex (Π₀ i, α i)) :=
  {
    Lex.partialOrder with
    le_total :=
      ltTrichotomyRec (fun f g h => Or.inl h.le) (fun f g h => Or.inl h.le) fun f g h => Or.inr h.le
    decidableLt := by infer_instance
    decidableLe := by infer_instance
    DecidableEq := by infer_instance }
#align dfinsupp.lex.linear_order DFinsupp.Lex.linearOrder
-/

end LinearOrder

variable [∀ i, PartialOrder (α i)]

#print DFinsupp.toLex_monotone /-
theorem toLex_monotone : Monotone (@toLex (Π₀ i, α i)) := fun a b h =>
  le_of_lt_or_eq <| Classical.or_iff_not_imp_right.2 fun hne => by classical
#align dfinsupp.to_lex_monotone DFinsupp.toLex_monotone
-/

#print DFinsupp.lt_of_forall_lt_of_lt /-
theorem lt_of_forall_lt_of_lt (a b : Lex (Π₀ i, α i)) (i : ι) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b := fun h1 h2 => ⟨i, h1, h2⟩
#align dfinsupp.lt_of_forall_lt_of_lt DFinsupp.lt_of_forall_lt_of_lt
-/

end Zero

section Covariants

variable [LinearOrder ι] [∀ i, AddMonoid (α i)] [∀ i, LinearOrder (α i)]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `covariant_class` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `lex (Π₀ i, α i)` may fail to be
monotone, when it is "just" monotone on `α i`. -/


section Left

variable [∀ i, CovariantClass (α i) (α i) (· + ·) (· < ·)]

#print DFinsupp.Lex.covariantClass_lt_left /-
instance Lex.covariantClass_lt_left :
    CovariantClass (Lex (Π₀ i, α i)) (Lex (Π₀ i, α i)) (· + ·) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg ((· + ·) _) (lta j ja), add_lt_add_left ha _⟩⟩
#align dfinsupp.lex.covariant_class_lt_left DFinsupp.Lex.covariantClass_lt_left
-/

#print DFinsupp.Lex.covariantClass_le_left /-
instance Lex.covariantClass_le_left :
    CovariantClass (Lex (Π₀ i, α i)) (Lex (Π₀ i, α i)) (· + ·) (· ≤ ·) :=
  Add.to_covariantClass_left _
#align dfinsupp.lex.covariant_class_le_left DFinsupp.Lex.covariantClass_le_left
-/

end Left

section Right

variable [∀ i, CovariantClass (α i) (α i) (Function.swap (· + ·)) (· < ·)]

#print DFinsupp.Lex.covariantClass_lt_right /-
instance Lex.covariantClass_lt_right :
    CovariantClass (Lex (Π₀ i, α i)) (Lex (Π₀ i, α i)) (Function.swap (· + ·)) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩
#align dfinsupp.lex.covariant_class_lt_right DFinsupp.Lex.covariantClass_lt_right
-/

#print DFinsupp.Lex.covariantClass_le_right /-
instance Lex.covariantClass_le_right :
    CovariantClass (Lex (Π₀ i, α i)) (Lex (Π₀ i, α i)) (Function.swap (· + ·)) (· ≤ ·) :=
  Add.to_covariantClass_right _
#align dfinsupp.lex.covariant_class_le_right DFinsupp.Lex.covariantClass_le_right
-/

end Right

end Covariants

end DFinsupp

