import Mathbin.RingTheory.Noetherian 
import Mathbin.RingTheory.JacobsonIdeal

/-!
# Nakayama's lemma

This file contains some alternative statements of Nakayama's Lemma as found in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

## Main statements

* `submodule.eq_smul_of_le_smul_of_le_jacobson` - A version of (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `submodule.eq_bot_of_le_smul_of_le_jacobson_bot` - Statement (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).,
  generalising to the Jacobson of any ideal.
* `submodule.smul_sup_eq_of_le_smul_of_le_jacobson_bot` - Statement (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

Note that a version of Statement (1) in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV) can be found in
`ring_theory/noetherian` under the name
`submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`

## References
* [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)

## Tags
Nakayama, Jacobson
-/


variable{R M : Type _}[CommRingₓ R][AddCommGroupₓ M][Module R M]

open Ideal

namespace Submodule

-- error in RingTheory.Nakayama: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- *Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
theorem eq_smul_of_le_smul_of_le_jacobson
{I J : ideal R}
{N : submodule R M}
(hN : N.fg)
(hIN : «expr ≤ »(N, «expr • »(I, N)))
(hIjac : «expr ≤ »(I, jacobson J)) : «expr = »(N, «expr • »(J, N)) :=
begin
  refine [expr le_antisymm _ (submodule.smul_le.2 (λ _ _ _, submodule.smul_mem _ _))],
  intros [ident n, ident hn],
  cases [expr submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN] ["with", ident r, ident hr],
  cases [expr exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1)] ["with", ident s, ident hs],
  have [] [":", expr «expr = »(n, «expr • »(«expr- »(«expr - »(«expr * »(r, s), 1)), n))] [],
  { rw ["[", expr neg_sub, ",", expr sub_smul, ",", expr mul_comm, ",", expr mul_smul, ",", expr hr.2 n hn, ",", expr one_smul, ",", expr smul_zero, ",", expr sub_zero, "]"] [] },
  rw [expr this] [],
  exact [expr submodule.smul_mem_smul (submodule.neg_mem _ hs) hn]
end

/-- *Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
theorem eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.fg) (hIN : N ≤ I • N)
  (hIjac : I ≤ jacobson ⊥) : N = ⊥ :=
  by 
    rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, Submodule.bot_smul]

-- error in RingTheory.Nakayama: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- *Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`.  -/
theorem smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
{I J : ideal R}
{N N' : submodule R M}
(hN' : N'.fg)
(hIJ : «expr ≤ »(I, jacobson J))
(hNN : «expr ≤ »(«expr ⊔ »(N, N'), «expr ⊔ »(N, «expr • »(I, N')))) : «expr = »(«expr ⊔ »(N, «expr • »(I, N')), «expr ⊔ »(N, «expr • »(J, N'))) :=
begin
  have [ident hNN'] [":", expr «expr = »(«expr ⊔ »(N, N'), «expr ⊔ »(N, «expr • »(I, N')))] [],
  from [expr le_antisymm hNN (sup_le_sup_left (submodule.smul_le.2 (λ _ _ _, submodule.smul_mem _ _)) _)],
  have [] [":", expr «expr = »(«expr • »(I, N').map N.mkq, N'.map N.mkq)] [],
  { rw ["<-", expr (submodule.comap_injective_of_surjective (linear_map.range_eq_top.1 (submodule.range_mkq N))).eq_iff] [],
    simpa [] [] [] ["[", expr comap_map_eq, ",", expr sup_comm, ",", expr eq_comm, "]"] [] ["using", expr hNN'] },
  have [] [] [":=", expr @submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J (N'.map N.mkq) (fg_map hN') (by rw ["[", "<-", expr map_smul'', ",", expr this, "]"] []; exact [expr le_refl _]) hIJ],
  rw ["[", "<-", expr map_smul'', ",", "<-", expr (submodule.comap_injective_of_surjective (linear_map.range_eq_top.1 (submodule.range_mkq N))).eq_iff, ",", expr comap_map_eq, ",", expr comap_map_eq, ",", expr submodule.ker_mkq, ",", expr sup_comm, ",", expr hNN', "]"] ["at", ident this],
  rw ["[", expr this, ",", expr sup_comm, "]"] []
end

/-- *Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
theorem smul_sup_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN' : N'.fg)
  (hIJ : I ≤ jacobson ⊥) (hNN : N⊔N' ≤ N⊔I • N') : I • N' ≤ N :=
  by 
    rw [←sup_eq_left, smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN' hIJ hNN, bot_smul, sup_bot_eq]

end Submodule

