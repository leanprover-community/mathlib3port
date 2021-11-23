import Mathbin.Data.Fintype.Basic 
import Mathbin.Data.Set.Finite

/-!
# Hall's Marriage Theorem for finite index types

This module proves the basic form of Hall's theorem.
In constrast to the theorem described in `combinatorics.hall.basic`, this
version requires that the indexed family `t : ι → finset α` have `ι` be a `fintype`.
The `combinatorics.hall.basic` module applies a compactness argument to this version
to remove the `fintype` constraint on `ι`.

The modules are split like this since the generalized statement
depends on the topology and category theory libraries, but the finite
case in this module has few dependencies.

A description of this formalization is in [Gusakov2021].

## Main statements

* `finset.all_card_le_bUnion_card_iff_exists_injective'` is Hall's theorem with
  a finite index set.  This is elsewhere generalized to
  `finset.all_card_le_bUnion_card_iff_exists_injective`.

## Tags

Hall's Marriage Theorem, indexed families
-/


open Finset

universe u v

namespace HallMarriageTheorem

variable{ι : Type u}{α : Type v}[Fintype ι]

theorem hall_hard_inductive_zero (t : ι → Finset α) (hn : Fintype.card ι = 0) :
  ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  by 
    rw [Fintype.card_eq_zero_iff] at hn 
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩

variable{t : ι → Finset α}[DecidableEq α]

-- error in Combinatorics.Hall.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hall_cond_of_erase
{x : ι}
(a : α)
(ha : ∀ s : finset ι, s.nonempty → «expr ≠ »(s, univ) → «expr < »(s.card, (s.bUnion t).card))
(s' : finset {x' : ι | «expr ≠ »(x', x)}) : «expr ≤ »(s'.card, (s'.bUnion (λ x', (t x').erase a)).card) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  specialize [expr ha (s'.image coe)],
  rw ["[", expr nonempty.image_iff, ",", expr finset.card_image_of_injective s' subtype.coe_injective, "]"] ["at", ident ha],
  by_cases [expr he, ":", expr s'.nonempty],
  { have [ident ha'] [":", expr «expr < »(s'.card, (s'.bUnion (λ x, t x)).card)] [],
    { specialize [expr ha he (λ h, by { have [ident h'] [] [":=", expr mem_univ x],
          rw ["<-", expr h] ["at", ident h'],
          simpa [] [] [] [] [] ["using", expr h'] })],
      convert [] [expr ha] ["using", 2],
      ext [] [ident x] [],
      simp [] [] ["only"] ["[", expr mem_image, ",", expr mem_bUnion, ",", expr exists_prop, ",", expr set_coe.exists, ",", expr exists_and_distrib_right, ",", expr exists_eq_right, ",", expr subtype.coe_mk, "]"] [] [] },
    rw ["<-", expr erase_bUnion] [],
    by_cases [expr hb, ":", expr «expr ∈ »(a, s'.bUnion (λ x, t x))],
    { rw [expr card_erase_of_mem hb] [],
      exact [expr nat.le_pred_of_lt ha'] },
    { rw [expr erase_eq_of_not_mem hb] [],
      exact [expr nat.le_of_lt ha'] } },
  { rw ["[", expr nonempty_iff_ne_empty, ",", expr not_not, "]"] ["at", ident he],
    subst [expr s'],
    simp [] [] [] [] [] [] }
end

-- error in Combinatorics.Hall.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
First case of the inductive step: assuming that
`∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem hall_hard_inductive_step_A
{n : exprℕ()}
(hn : «expr = »(fintype.card ι, «expr + »(n, 1)))
(ht : ∀ s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card))
(ih : ∀
 {ι' : Type u}
 [fintype ι']
 (t' : ι' → finset α), by exactI [expr «expr ≤ »(fintype.card ι', n) → ∀
  s' : finset ι', «expr ≤ »(s'.card, (s'.bUnion t').card) → «expr∃ , »((f : ι' → α), «expr ∧ »(function.injective f, ∀
    x, «expr ∈ »(f x, t' x)))])
(ha : ∀
 s : finset ι, s.nonempty → «expr ≠ »(s, univ) → «expr < »(s.card, (s.bUnion t).card)) : «expr∃ , »((f : ι → α), «expr ∧ »(function.injective f, ∀
  x, «expr ∈ »(f x, t x))) :=
begin
  haveI [] [":", expr nonempty ι] [":=", expr fintype.card_pos_iff.mp «expr ▸ »(hn.symm, nat.succ_pos _)],
  haveI [] [] [":=", expr classical.dec_eq ι],
  let [ident x] [] [":=", expr classical.arbitrary ι],
  have [ident tx_ne] [":", expr (t x).nonempty] [],
  { rw ["<-", expr finset.card_pos] [],
    apply [expr nat.lt_of_lt_of_le nat.one_pos],
    convert [] [expr ht {x}] [],
    rw [expr finset.singleton_bUnion] [] },
  rcases [expr classical.indefinite_description _ tx_ne, "with", "⟨", ident y, ",", ident hy, "⟩"],
  let [ident ι'] [] [":=", expr {x' : ι | «expr ≠ »(x', x)}],
  let [ident t'] [":", expr ι' → finset α] [":=", expr λ x', (t x').erase y],
  have [ident card_ι'] [":", expr «expr = »(fintype.card ι', n)] [],
  { convert [] [expr congr_arg (λ m, «expr - »(m, 1)) hn] [],
    convert [] [expr set.card_ne_eq _] [] },
  rcases [expr ih t' card_ι'.le (hall_cond_of_erase y ha), "with", "⟨", ident f', ",", ident hfinj, ",", ident hfr, "⟩"],
  refine [expr ⟨λ z, if h : «expr = »(z, x) then y else f' ⟨z, h⟩, _, _⟩],
  { rintro [ident z₁, ident z₂],
    have [ident key] [":", expr ∀ {x}, «expr ≠ »(y, f' x)] [],
    { intros [ident x, ident h],
      specialize [expr hfr x],
      rw ["<-", expr h] ["at", ident hfr],
      simpa [] [] [] [] [] ["using", expr hfr] },
    by_cases [expr h₁, ":", expr «expr = »(z₁, x)]; by_cases [expr h₂, ":", expr «expr = »(z₂, x)]; simp [] [] [] ["[", expr h₁, ",", expr h₂, ",", expr hfinj.eq_iff, ",", expr key, ",", expr key.symm, "]"] [] [] },
  { intro [ident z],
    split_ifs [] ["with", ident hz],
    { rwa [expr hz] [] },
    { specialize [expr hfr ⟨z, hz⟩],
      rw [expr mem_erase] ["at", ident hfr],
      exact [expr hfr.2] } }
end

-- error in Combinatorics.Hall.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hall_cond_of_restrict
{ι : Type u}
{t : ι → finset α}
{s : finset ι}
(ht : ∀ s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card))
(s' : finset (s : set ι)) : «expr ≤ »(s'.card, (s'.bUnion (λ a', t a')).card) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  convert [] [expr ht (s'.image coe)] ["using", 1],
  { rw [expr card_image_of_injective _ subtype.coe_injective] [] },
  { apply [expr congr_arg],
    ext [] [ident y] [],
    simp [] [] [] [] [] [] }
end

-- error in Combinatorics.Hall.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hall_cond_of_compl
{ι : Type u}
{t : ι → finset α}
{s : finset ι}
(hus : «expr = »(s.card, (s.bUnion t).card))
(ht : ∀ s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card))
(s' : finset («expr ᶜ»(s) : set ι)) : «expr ≤ »(s'.card, (s'.bUnion (λ x', «expr \ »(t x', s.bUnion t))).card) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  have [] [":", expr «expr = »(s'.card, «expr - »(«expr ∪ »(s, s'.image coe).card, s.card))] [],
  { rw ["[", expr card_disjoint_union, ",", expr add_tsub_cancel_left, ",", expr card_image_of_injective _ subtype.coe_injective, "]"] [],
    simp [] [] ["only"] ["[", expr disjoint_left, ",", expr not_exists, ",", expr mem_image, ",", expr exists_prop, ",", expr set_coe.exists, ",", expr exists_and_distrib_right, ",", expr exists_eq_right, ",", expr subtype.coe_mk, "]"] [] [],
    intros [ident x, ident hx, ident hc, ident h],
    exact [expr (hc hx).elim] },
  rw ["[", expr this, ",", expr hus, "]"] [],
  apply [expr (tsub_le_tsub_right (ht _) _).trans _],
  rw ["<-", expr card_sdiff] [],
  { have [] [":", expr «expr ⊆ »(«expr \ »(«expr ∪ »(s, s'.image subtype.val).bUnion t, s.bUnion t), s'.bUnion (λ
       x', «expr \ »(t x', s.bUnion t)))] [],
    { intros [ident t],
      simp [] [] ["only"] ["[", expr mem_bUnion, ",", expr mem_sdiff, ",", expr not_exists, ",", expr mem_image, ",", expr and_imp, ",", expr mem_union, ",", expr exists_and_distrib_right, ",", expr exists_imp_distrib, "]"] [] [],
      rintro [ident x, "(", ident hx, "|", "⟨", ident x', ",", ident hx', ",", ident rfl, "⟩", ")", ident rat, ident hs],
      { exact [expr (hs x hx rat).elim] },
      { exact [expr ⟨⟨x', hx', rat⟩, hs⟩] } },
    exact [expr (card_le_of_subset this).trans le_rfl] },
  { apply [expr bUnion_subset_bUnion_of_subset_left],
    apply [expr subset_union_left] }
end

-- error in Combinatorics.Hall.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Second case of the inductive step: assuming that
`∃ (s : finset ι), s ≠ univ → s.card = (s.bUnion t).card`
and that the statement of Hall's Marriage Theorem is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem hall_hard_inductive_step_B
{n : exprℕ()}
(hn : «expr = »(fintype.card ι, «expr + »(n, 1)))
(ht : ∀ s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card))
(ih : ∀
 {ι' : Type u}
 [fintype ι']
 (t' : ι' → finset α), by exactI [expr «expr ≤ »(fintype.card ι', n) → ∀
  s' : finset ι', «expr ≤ »(s'.card, (s'.bUnion t').card) → «expr∃ , »((f : ι' → α), «expr ∧ »(function.injective f, ∀
    x, «expr ∈ »(f x, t' x)))])
(s : finset ι)
(hs : s.nonempty)
(hns : «expr ≠ »(s, univ))
(hus : «expr = »(s.card, (s.bUnion t).card)) : «expr∃ , »((f : ι → α), «expr ∧ »(function.injective f, ∀
  x, «expr ∈ »(f x, t x))) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  let [ident t'] [":", expr s → finset α] [":=", expr λ x', t x'],
  rw [expr nat.add_one] ["at", ident hn],
  have [ident card_ι'_le] [":", expr «expr ≤ »(fintype.card s, n)] [],
  { apply [expr nat.le_of_lt_succ],
    rw ["<-", expr hn] [],
    convert [] [expr (card_lt_iff_ne_univ _).mpr hns] [],
    convert [] [expr fintype.card_coe _] [] },
  rcases [expr ih t' card_ι'_le (hall_cond_of_restrict ht), "with", "⟨", ident f', ",", ident hf', ",", ident hsf', "⟩"],
  set [] [ident ι''] [] [":="] [expr «expr ᶜ»((s : set ι))] ["with", ident ι''_def],
  let [ident t''] [":", expr ι'' → finset α] [":=", expr λ a'', «expr \ »(t a'', s.bUnion t)],
  have [ident card_ι''_le] [":", expr «expr ≤ »(fintype.card ι'', n)] [],
  { apply [expr nat.le_of_lt_succ],
    rw ["<-", expr hn] [],
    convert [] [expr (card_compl_lt_iff_nonempty _).mpr hs] [],
    convert [] [expr fintype.card_coe «expr ᶜ»(s)] [],
    exact [expr (finset.coe_compl s).symm] },
  rcases [expr ih t'' card_ι''_le (hall_cond_of_compl hus ht), "with", "⟨", ident f'', ",", ident hf'', ",", ident hsf'', "⟩"],
  have [ident f'_mem_bUnion] [":", expr ∀ {x'} (hx' : «expr ∈ »(x', s)), «expr ∈ »(f' ⟨x', hx'⟩, s.bUnion t)] [],
  { intros [ident x', ident hx'],
    rw [expr mem_bUnion] [],
    exact [expr ⟨x', hx', hsf' _⟩] },
  have [ident f''_not_mem_bUnion] [":", expr ∀
   {x''}
   (hx'' : «expr¬ »(«expr ∈ »(x'', s))), «expr¬ »(«expr ∈ »(f'' ⟨x'', hx''⟩, s.bUnion t))] [],
  { intros [ident x'', ident hx''],
    have [ident h] [] [":=", expr hsf'' ⟨x'', hx''⟩],
    rw [expr mem_sdiff] ["at", ident h],
    exact [expr h.2] },
  have [ident im_disj] [":", expr ∀
   {x' x'' : ι}
   {hx' : «expr ∈ »(x', s)}
   {hx'' : «expr¬ »(«expr ∈ »(x'', s))}, «expr ≠ »(f' ⟨x', hx'⟩, f'' ⟨x'', hx''⟩)] [],
  { intros ["_", "_", ident hx', ident hx'', ident h],
    apply [expr f''_not_mem_bUnion hx''],
    rw ["<-", expr h] [],
    apply [expr f'_mem_bUnion] },
  refine [expr ⟨λ x, if h : «expr ∈ »(x, s) then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩],
  { exact [expr hf'.dite _ hf'' @im_disj] },
  { intro [ident x],
    split_ifs [] [],
    { exact [expr hsf' ⟨x, h⟩] },
    { exact [expr sdiff_subset _ _ (hsf'' ⟨x, h⟩)] } }
end

-- error in Combinatorics.Hall.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `ι` has cardinality `n + 1` and the statement of Hall's Marriage Theorem
is true for all `ι'` of cardinality ≤ `n`, then it is true for `ι`.
-/
theorem hall_hard_inductive_step
{n : exprℕ()}
(hn : «expr = »(fintype.card ι, «expr + »(n, 1)))
(ht : ∀ s : finset ι, «expr ≤ »(s.card, (s.bUnion t).card))
(ih : ∀
 {ι' : Type u}
 [fintype ι']
 (t' : ι' → finset α), by exactI [expr «expr ≤ »(fintype.card ι', n) → ∀
  s' : finset ι', «expr ≤ »(s'.card, (s'.bUnion t').card) → «expr∃ , »((f : ι' → α), «expr ∧ »(function.injective f, ∀
    x, «expr ∈ »(f x, t' x)))]) : «expr∃ , »((f : ι → α), «expr ∧ »(function.injective f, ∀ x, «expr ∈ »(f x, t x))) :=
begin
  by_cases [expr h, ":", expr ∀ s : finset ι, s.nonempty → «expr ≠ »(s, univ) → «expr < »(s.card, (s.bUnion t).card)],
  { exact [expr hall_hard_inductive_step_A hn ht @ih h] },
  { push_neg ["at", ident h],
    rcases [expr h, "with", "⟨", ident s, ",", ident sne, ",", ident snu, ",", ident sle, "⟩"],
    have [ident seq] [] [":=", expr nat.le_antisymm (ht _) sle],
    exact [expr hall_hard_inductive_step_B hn ht @ih s sne snu seq] }
end

/--
Here we combine the base case and the inductive step into
a full strong induction proof, thus completing the proof
of the second direction.
-/
theorem hall_hard_inductive {n : ℕ} (hn : Fintype.card ι = n) (ht : ∀ s : Finset ι, s.card ≤ (s.bUnion t).card) :
  ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  by 
    runTac 
      tactic.unfreeze_local_instances 
    revert ι 
    refine' Nat.strong_induction_onₓ n fun n' ih => _ 
    intro _ _ t hn ht 
    rcases n' with (_ | _)
    ·
      exact hall_hard_inductive_zero t hn
    ·
      apply hall_hard_inductive_step hn ht 
      intros ι' _ _ hι' 
      exact ih (Fintype.card ι') (Nat.lt_succ_of_leₓ hι') rfl

end HallMarriageTheorem

/--
This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α` with `ι` a `fintype`.
It states that there is a set of distinct representatives if and only
if every union of `k` of the sets has at least `k` elements.

See `finset.all_card_le_bUnion_card_iff_exists_injective` for a version
where the `fintype ι` constraint is removed.
-/
theorem Finset.all_card_le_bUnion_card_iff_exists_injective' {ι α : Type _} [Fintype ι] [DecidableEq α]
  (t : ι → Finset α) :
  (∀ s : Finset ι, s.card ≤ (s.bUnion t).card) ↔ ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  by 
    split 
    ·
      exact HallMarriageTheorem.hall_hard_inductive rfl
    ·
      rintro ⟨f, hf₁, hf₂⟩ s 
      rw [←card_image_of_injective s hf₁]
      apply card_le_of_subset 
      intro 
      rw [mem_image, mem_bUnion]
      rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hf₂ x⟩

