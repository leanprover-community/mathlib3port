import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Sym.Sym2

/-!
# Stars and bars

In this file, we prove the case `n = 2` of stars and bars.

## Informal statement

If we have `n` objects to put in `k` boxes, we can do so in exactly `(n + k - 1).choose n` ways.

## Formal statement

We can identify the `k` boxes with the elements of a fintype `α` of card `k`. Then placing `n`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `n`. `sym α n` being the subtype of `multiset α` of multisets of card `n`, writing stars
and bars using types gives
```lean
-- TODO: this lemma is not yet proven
lemma stars_and_bars {α : Type*} [fintype α] (n : ℕ) :
  card (sym α n) = (card α + n - 1).choose (card α) := sorry
```

## TODO

Prove the general case of stars and bars.

## Tags

stars and bars
-/


open Finset Fintype

namespace Sym2

variable {α : Type _} [DecidableEq α]

/-- The `diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card`. -/
theorem card_image_diag (s : Finset α) : (s.diag.image Quotientₓ.mk).card = s.card :=
  by 
    rw [card_image_of_inj_on, diag_card]
    rintro ⟨x₀, x₁⟩ hx _ _ h 
    cases Quotientₓ.eq.1 h
    ·
      rfl
    ·
      simp only [mem_coe, mem_diag] at hx 
      rw [hx.2]

-- error in Data.Sym.Card: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem two_mul_card_image_off_diag
(s : finset α) : «expr = »(«expr * »(2, (s.off_diag.image quotient.mk).card), s.off_diag.card) :=
begin
  rw ["[", expr card_eq_sum_card_fiberwise (λ
   x, mem_image_of_mem _ : ∀
   x «expr ∈ » s.off_diag, «expr ∈ »(quotient.mk x, s.off_diag.image quotient.mk)), ",", expr sum_const_nat (quotient.ind _), ",", expr mul_comm, "]"] [],
  rintro ["⟨", ident x, ",", ident y, "⟩", ident hxy],
  simp_rw ["[", expr mem_image, ",", expr exists_prop, ",", expr mem_off_diag, ",", expr quotient.eq, "]"] ["at", ident hxy],
  obtain ["⟨", ident a, ",", "⟨", ident ha₁, ",", ident ha₂, ",", ident ha, "⟩", ",", ident h, "⟩", ":=", expr hxy],
  obtain ["⟨", ident hx, ",", ident hy, ",", ident hxy, "⟩", ":", expr «expr ∧ »(«expr ∈ »(x, s), «expr ∧ »(«expr ∈ »(y, s), «expr ≠ »(x, y)))],
  { cases [expr h] []; have [] [] [":=", expr ha.symm]; exact [expr ⟨«expr‹ ›»(_), «expr‹ ›»(_), «expr‹ ›»(_)⟩] },
  have [ident hxy'] [":", expr «expr ≠ »(y, x)] [":=", expr hxy.symm],
  have [] [":", expr «expr = »(s.off_diag.filter (λ
     z, «expr = »(«expr⟦ ⟧»(z), «expr⟦ ⟧»((x, y)))), ({(x, y), (y, x)} : finset _))] [],
  { ext [] ["⟨", ident x₁, ",", ident y₁, "⟩"] [],
    rw ["[", expr mem_filter, ",", expr mem_insert, ",", expr mem_singleton, ",", expr sym2.eq_iff, ",", expr prod.mk.inj_iff, ",", expr prod.mk.inj_iff, ",", expr and_iff_right_iff_imp, "]"] [],
    rintro ["(", "⟨", ident rfl, ",", ident rfl, "⟩", "|", "⟨", ident rfl, ",", ident rfl, "⟩", ")"]; rw [expr mem_off_diag] []; exact [expr ⟨«expr‹ ›»(_), «expr‹ ›»(_), «expr‹ ›»(_)⟩] },
  rw ["[", expr this, ",", expr card_insert_of_not_mem, ",", expr card_singleton, "]"] [],
  simp [] [] ["only"] ["[", expr not_and, ",", expr prod.mk.inj_iff, ",", expr mem_singleton, "]"] [] [],
  exact [expr λ _, hxy']
end

/-- The `off_diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.off_diag.card / 2`.
This is because every element `⟦(x, y)⟧` of `sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
theorem card_image_off_diag (s : Finset α) : (s.off_diag.image Quotientₓ.mk).card = s.card.choose 2 :=
  by 
    rw [Nat.choose_two_right, mul_tsub, mul_oneₓ, ←off_diag_card,
      Nat.div_eq_of_eq_mul_rightₓ zero_lt_two (two_mul_card_image_off_diag s).symm]

theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.is_diag } = card α :=
  by 
    convert card_image_diag (univ : Finset α)
    rw [Fintype.card_of_subtype, ←filter_image_quotient_mk_is_diag]
    rintro x 
    rw [mem_filter, univ_product_univ, mem_image]
    obtain ⟨a, ha⟩ := Quotientₓ.exists_rep x 
    exact and_iff_right ⟨a, mem_univ _, ha⟩

theorem card_subtype_not_diag [Fintype α] : card { a : Sym2 α // ¬a.is_diag } = (card α).choose 2 :=
  by 
    convert card_image_off_diag (univ : Finset α)
    rw [Fintype.card_of_subtype, ←filter_image_quotient_mk_not_is_diag]
    rintro x 
    rw [mem_filter, univ_product_univ, mem_image]
    obtain ⟨a, ha⟩ := Quotientₓ.exists_rep x 
    exact and_iff_right ⟨a, mem_univ _, ha⟩

protected theorem card [Fintype α] : card (Sym2 α) = (card α*card α+1) / 2 :=
  by 
    rw [←Fintype.card_congr (@Equiv.sumCompl _ is_diag (Sym2.IsDiag.decidablePred α)), Fintype.card_sum,
      card_subtype_diag, card_subtype_not_diag, Nat.choose_two_right, add_commₓ, ←Nat.triangle_succ, Nat.succ_sub_one,
      mul_commₓ]

end Sym2

