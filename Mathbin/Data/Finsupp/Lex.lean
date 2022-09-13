/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Data.Pi.Lex
import Mathbin.Data.Finsupp.Order
import Mathbin.Data.Finsupp.NeLocus

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `finsupp`.
-/


variable {α N : Type _}

namespace Finsupp

section NHasZero

variable [Zero N]

/-- `finsupp.lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `_root_.lex (α →₀ N)` has an order given by `finsupp.lex (<) (<)`.
-/
protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r (fun _ => s) x y

theorem _root_.pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
    Pi.Lex r (fun _ => s) (a : α → N) (b : α → N) = Finsupp.Lex r s a b :=
  rfl

theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  Iff.rfl

instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g => Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

instance Lex.is_strict_order [LinearOrderₓ α] [PartialOrderₓ N] : IsStrictOrder (Lex (α →₀ N)) (· < ·) :=
  let i : IsStrictOrder (Lex (α → N)) (· < ·) := Pi.Lex.is_strict_order
  { irrefl := toLex.Surjective.forall.2 fun a => @irrefl _ _ i.to_is_irrefl a,
    trans := toLex.Surjective.forall₃.2 fun a b c => @trans _ _ i.to_is_trans a b c }

variable [LinearOrderₓ α]

/-- The partial order on `finsupp`s obtained by the lexicographic ordering.
See `finsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [PartialOrderₓ N] : PartialOrderₓ (Lex (α →₀ N)) :=
  PartialOrderₓ.lift (fun x => toLex ⇑(ofLex x)) Finsupp.coe_fn_injective

--fun_like.coe_injective
variable [LinearOrderₓ N]

/-- Auxiliary helper to case split computably. There is no need for this to be public, as it
can be written with `or.by_cases` on `lt_trichotomy` once the instances below are constructed. -/
private def lt_trichotomy_rec {P : Lex (α →₀ N) → Lex (α →₀ N) → Sort _}
    (h_lt : ∀ {f g}, toLex f < toLex g → P (toLex f) (toLex g))
    (h_eq : ∀ {f g}, toLex f = toLex g → P (toLex f) (toLex g))
    (h_gt : ∀ {f g}, toLex g < toLex f → P (toLex f) (toLex g)) : ∀ f g, P f g :=
  Lex.rec fun f =>
    Lex.rec fun g =>
      match (motive := ∀ y, (f.neLocus g).min = y → _) _, rfl with
      | ⊤, h => h_eq (Finsupp.ne_locus_eq_empty.mp (Finset.min_eq_top.mp h))
      | (wit : α), h =>
        have hne : f wit ≠ g wit := mem_ne_locus.mp (Finset.mem_of_min h)
        hne.lt_or_lt.byCases
          (fun hwit => h_lt ⟨wit, fun j hj => mem_ne_locus.not_left.mp (Finset.not_mem_of_lt_min hj h), hwit⟩)
          fun hwit =>
          h_gt
            ⟨wit, fun j hj => by
              refine' mem_ne_locus.not_left.mp (Finset.not_mem_of_lt_min hj _)
              rwa [ne_locus_comm], hwit⟩

-- ./././Mathport/Syntax/Translate/Command.lean:271:38: unsupported irreducible non-definition
irreducible_def Lex.decidableLe : @DecidableRel (Lex (α →₀ N)) (· ≤ ·) :=
  ltTrichotomyRec (fun f g h => is_true <| Or.inr h) (fun f g h => is_true <| Or.inl <| congr_arg _ h) fun f g h =>
    is_false fun h' => (lt_irreflₓ _ (h.trans_le h')).elim

-- ./././Mathport/Syntax/Translate/Command.lean:271:38: unsupported irreducible non-definition
irreducible_def Lex.decidableLt : @DecidableRel (Lex (α →₀ N)) (· < ·) :=
  ltTrichotomyRec (fun f g h => isTrue h) (fun f g h => isFalse h.not_lt) fun f g h => isFalse h.asymm

/-- The linear order on `finsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder : LinearOrderₓ (Lex (α →₀ N)) :=
  { Lex.partialOrder with
    le_total := ltTrichotomyRec (fun f g h => Or.inl h.le) (fun f g h => Or.inl h.le) fun f g h => Or.inr h.le,
    decidableLt := by
      infer_instance,
    decidableLe := by
      infer_instance,
    DecidableEq := by
      infer_instance }

theorem Lex.le_of_forall_le {a b : Lex (α →₀ N)} (h : ∀ i, ofLex a i ≤ ofLex b i) : a ≤ b :=
  le_of_not_ltₓ fun ⟨i, hi⟩ => (h i).not_lt hi.2

theorem Lex.le_of_of_lex_le {a b : Lex (α →₀ N)} (h : ofLex a ≤ ofLex b) : a ≤ b :=
  Lex.le_of_forall_le h

theorem to_lex_monotone : Monotone (@toLex (α →₀ N)) := fun _ _ => Lex.le_of_forall_le

theorem lt_of_forall_lt_of_lt (a b : Lex (α →₀ N)) (i : α) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b := fun h1 h2 => ⟨i, h1, h2⟩

end NHasZero

section Covariants

variable [LinearOrderₓ α] [AddMonoidₓ N] [LinearOrderₓ N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `covariant_class` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `lex (α →₀ N)` may fail to be
monotone, when it is "just" monotone on `N`. -/


section Left

variable [CovariantClass N N (· + ·) (· < ·)]

instance Lex.covariant_class_lt_left : CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg ((· + ·) _) (lta j ja), add_lt_add_left ha _⟩⟩

instance Lex.covariant_class_le_left : CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· ≤ ·) :=
  Add.to_covariant_class_left _

end Left

section Right

variable [CovariantClass N N (Function.swap (· + ·)) (· < ·)]

instance Lex.covariant_class_lt_right : CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ => ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩

instance Lex.covariant_class_le_right : CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· ≤ ·) :=
  Add.to_covariant_class_right _

end Right

end Covariants

end Finsupp

