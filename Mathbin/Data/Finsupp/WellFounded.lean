/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module data.finsupp.well_founded
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Dfinsupp.WellFounded
import Mathbin.Data.Finsupp.Lex

/-!
# Well-foundedness of the lexicographic and product orders on `finsupp`

`finsupp.lex.well_founded` and the two variants that follow it essentially say that if
`(>)` is a well order on `α`, `(<)` is well-founded on `N`, and `0` is a bottom element in `N`,
then the lexicographic `(<)` is well-founded on `α →₀ N`.

`finsupp.lex.well_founded_lt_of_finite` says that if `α` is finite and equipped with a linear
order and `(<)` is well-founded on `N`, then the lexicographic `(<)` is well-founded on `α →₀ N`.

`finsupp.well_founded_lt` and `well_founded_lt_of_finite` state the same results for the product
order `(<)`, but without the ordering conditions on `α`.

All results are transferred from `dfinsupp` via `finsupp.to_dfinsupp`.
-/


variable {α N : Type _}

namespace Finsupp

variable [hz : Zero N] {r : α → α → Prop} {s : N → N → Prop} (hbot : ∀ ⦃n⦄, ¬s n 0)
  (hs : WellFounded s)

include hbot hs

/-- Transferred from `dfinsupp.lex.acc`. See the top of that file for an explanation for the
  appearance of the relation `rᶜ ⊓ (≠)`. -/
theorem Lex.acc (x : α →₀ N) (h : ∀ a ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) a) :
    Acc (Finsupp.Lex r s) x := by
  rw [lex_eq_inv_image_dfinsupp_lex]
  classical
    refine' InvImage.accessible to_dfinsupp (Dfinsupp.Lex.acc (fun a => hbot) (fun a => hs) _ _)
    simpa only [to_dfinsupp_support] using h
#align finsupp.lex.acc Finsupp.Lex.acc

theorem Lex.well_founded (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (Finsupp.Lex r s) :=
  ⟨fun x => (Lex.acc hbot hs x) fun a _ => hr.apply a⟩
#align finsupp.lex.well_founded Finsupp.Lex.well_founded

theorem Lex.well_founded' [IsTrichotomous α r] (hr : WellFounded r.swap) :
    WellFounded (Finsupp.Lex r s) :=
  (lex_eq_inv_image_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (Dfinsupp.Lex.well_founded' (fun a => hbot) (fun a => hs) hr)
#align finsupp.lex.well_founded' Finsupp.Lex.well_founded'

omit hbot hs

instance Lex.well_founded_lt [LT α] [IsTrichotomous α (· < ·)] [hα : WellFoundedGt α]
    [CanonicallyOrderedAddMonoid N] [hN : WellFoundedLt N] : WellFoundedLt (Lex (α →₀ N)) :=
  ⟨Lex.well_founded' (fun n => (zero_le n).not_lt) hN.wf hα.wf⟩
#align finsupp.lex.well_founded_lt Finsupp.Lex.well_founded_lt

variable (r)

theorem Lex.well_founded_of_finite [IsStrictTotalOrder α r] [Finite α] [Zero N]
    (hs : WellFounded s) : WellFounded (Finsupp.Lex r s) :=
  InvImage.wf (@equivFunOnFinite α N _ _) ((Pi.Lex.well_founded r) fun a => hs)
#align finsupp.lex.well_founded_of_finite Finsupp.Lex.well_founded_of_finite

theorem Lex.well_founded_lt_of_finite [LinearOrder α] [Finite α] [Zero N] [LT N]
    [hwf : WellFoundedLt N] : WellFoundedLt (Lex (α →₀ N)) :=
  ⟨Finsupp.Lex.well_founded_of_finite (· < ·) hwf.1⟩
#align finsupp.lex.well_founded_lt_of_finite Finsupp.Lex.well_founded_lt_of_finite

protected theorem well_founded_lt [Zero N] [Preorder N] [WellFoundedLt N] (hbot : ∀ n : N, ¬n < 0) :
    WellFoundedLt (α →₀ N) :=
  ⟨InvImage.wf toDfinsupp (Dfinsupp.well_founded_lt fun i a => hbot a).wf⟩
#align finsupp.well_founded_lt Finsupp.well_founded_lt

instance well_founded_lt' [CanonicallyOrderedAddMonoid N] [WellFoundedLt N] :
    WellFoundedLt (α →₀ N) :=
  Finsupp.well_founded_lt fun a => (zero_le a).not_lt
#align finsupp.well_founded_lt' Finsupp.well_founded_lt'

instance well_founded_lt_of_finite [Finite α] [Zero N] [Preorder N] [WellFoundedLt N] :
    WellFoundedLt (α →₀ N) :=
  ⟨InvImage.wf equivFunOnFinite Function.well_founded_lt.wf⟩
#align finsupp.well_founded_lt_of_finite Finsupp.well_founded_lt_of_finite

end Finsupp

