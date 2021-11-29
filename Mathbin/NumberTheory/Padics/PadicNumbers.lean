import Mathbin.Analysis.NormedSpace.Basic 
import Mathbin.NumberTheory.Padics.PadicNorm

/-!
# p-adic numbers

This file defines the p-adic numbers (rationals) `ℚ_p` as
the completion of `ℚ` with respect to the p-adic norm.
We show that the p-adic norm on ℚ extends to `ℚ_p`, that `ℚ` is embedded in `ℚ_p`,
and that `ℚ_p` is Cauchy complete.

## Important definitions

* `padic` : the type of p-adic numbers
* `padic_norm_e` : the rational valued p-adic norm on `ℚ_p`

## Notation

We introduce the notation `ℚ_[p]` for the p-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct ℝ.
`ℚ_p` inherits a field structure from this construction.
The extension of the norm on ℚ to `ℚ_p` is *not* analogous to extending the absolute value to ℝ,
and hence the proof that `ℚ_p` is complete is different from the proof that ℝ is complete.

A small special-purpose simplification tactic, `padic_index_simp`, is used to manipulate sequence
indices in the proof that the norm extends.

`padic_norm_e` is the rational-valued p-adic norm on `ℚ_p`.
To instantiate `ℚ_p` as a normed field, we must cast this into a ℝ-valued norm.
The `ℝ`-valued norm, using notation `∥ ∥` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padic_norm` to `padic_norm_e` when possible.
Since `padic_norm_e` and `∥ ∥` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/


noncomputable theory

open_locale Classical

open Nat multiplicity padicNorm CauSeq CauSeq.Completion Metric

/-- The type of Cauchy sequences of rationals with respect to the p-adic norm. -/
@[reducible]
def PadicSeq (p : ℕ) :=
  CauSeq _ (padicNorm p)

namespace PadicSeq

section 

variable {p : ℕ} [Fact p.prime]

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The p-adic norm of the entries of a nonzero Cauchy sequence of rationals is eventually
constant. -/
theorem stationary
{f : cau_seq exprℚ() (padic_norm p)}
(hf : «expr¬ »(«expr ≈ »(f, 0))) : «expr∃ , »((N), ∀
 m n, «expr ≤ »(N, m) → «expr ≤ »(N, n) → «expr = »(padic_norm p (f n), padic_norm p (f m))) :=
have «expr∃ , »((ε «expr > » 0), «expr∃ , »((N1), ∀
  j «expr ≥ » N1, «expr ≤ »(ε, padic_norm p (f j)))), from «expr $ »(cau_seq.abv_pos_of_not_lim_zero, not_lim_zero_of_not_congr_zero hf),
let ⟨ε, hε, N1, hN1⟩ := this, ⟨N2, hN2⟩ := cau_seq.cauchy₂ f hε in
⟨max N1 N2, λ
 n m hn hm, have «expr < »(padic_norm p «expr - »(f n, f m), ε), from hN2 _ _ (max_le_iff.1 hn).2 (max_le_iff.1 hm).2,
 have «expr < »(padic_norm p «expr - »(f n, f m), padic_norm p (f n)), from «expr $ »(lt_of_lt_of_le this, hN1 _ (max_le_iff.1 hn).1),
 have «expr < »(padic_norm p «expr - »(f n, f m), max (padic_norm p (f n)) (padic_norm p (f m))), from lt_max_iff.2 (or.inl this),
 begin
   by_contradiction [ident hne],
   rw ["<-", expr padic_norm.neg p (f m)] ["at", ident hne],
   have [ident hnam] [] [":=", expr add_eq_max_of_ne p hne],
   rw ["[", expr padic_norm.neg, ",", expr max_comm, "]"] ["at", ident hnam],
   rw ["[", "<-", expr hnam, ",", expr sub_eq_add_neg, ",", expr add_comm, "]"] ["at", ident this],
   apply [expr _root_.lt_irrefl _ this]
 end⟩

/-- For all n ≥ stationary_point f hf, the p-adic norm of f n is the same. -/
def stationary_point {f : PadicSeq p} (hf : ¬f ≈ 0) : ℕ :=
  Classical.some$ stationary hf

theorem stationary_point_spec {f : PadicSeq p} (hf : ¬f ≈ 0) :
  ∀ {m n}, stationary_point hf ≤ m → stationary_point hf ≤ n → padicNorm p (f n) = padicNorm p (f m) :=
  Classical.some_spec$ stationary hf

/-- Since the norm of the entries of a Cauchy sequence is eventually stationary,
we can lift the norm to sequences. -/
def norm (f : PadicSeq p) : ℚ :=
  if hf : f ≈ 0 then 0 else padicNorm p (f (stationary_point hf))

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_zero_iff (f : padic_seq p) : «expr ↔ »(«expr = »(f.norm, 0), «expr ≈ »(f, 0)) :=
begin
  constructor,
  { intro [ident h],
    by_contradiction [ident hf],
    unfold [ident norm] ["at", ident h],
    split_ifs ["at", ident h] [],
    apply [expr hf],
    intros [ident ε, ident hε],
    existsi [expr stationary_point hf],
    intros [ident j, ident hj],
    have [ident heq] [] [":=", expr stationary_point_spec hf (le_refl _) hj],
    simpa [] [] [] ["[", expr h, ",", expr heq, "]"] [] [] },
  { intro [ident h],
    simp [] [] [] ["[", expr norm, ",", expr h, "]"] [] [] }
end

end 

section Embedding

open CauSeq

variable {p : ℕ} [Fact p.prime]

theorem equiv_zero_of_val_eq_of_equiv_zero {f g : PadicSeq p} (h : ∀ k, padicNorm p (f k) = padicNorm p (g k))
  (hf : f ≈ 0) : g ≈ 0 :=
  fun ε hε =>
    let ⟨i, hi⟩ := hf _ hε
    ⟨i,
      fun j hj =>
        by 
          simpa [h] using hi _ hj⟩

theorem norm_nonzero_of_not_equiv_zero {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm ≠ 0 :=
  hf ∘ f.norm_zero_iff.1

theorem norm_eq_norm_app_of_nonzero {f : PadicSeq p} (hf : ¬f ≈ 0) : ∃ k, f.norm = padicNorm p k ∧ k ≠ 0 :=
  have heq : f.norm = padicNorm p (f$ stationary_point hf) :=
    by 
      simp [norm, hf]
  ⟨f$ stationary_point hf, HEq,
    fun h =>
      norm_nonzero_of_not_equiv_zero hf
        (by 
          simpa [h] using HEq)⟩

theorem not_lim_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬lim_zero (const (padicNorm p) q) :=
  fun h' => hq$ const_lim_zero.1 h'

theorem not_equiv_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬const (padicNorm p) q ≈ 0 :=
  fun h : lim_zero (const (padicNorm p) q - 0) =>
    not_lim_zero_const_of_nonzero hq$
      by 
        simpa using h

theorem norm_nonneg (f : PadicSeq p) : 0 ≤ f.norm :=
  if hf : f ≈ 0 then
    by 
      simp [hf, norm]
  else
    by 
      simp [norm, hf, padicNorm.nonneg]

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_left_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : ℕ) :
  padicNorm p (f (stationary_point hf)) = padicNorm p (f (max (stationary_point hf) (max v2 v3))) :=
  by 
    apply stationary_point_spec hf
    ·
      apply le_max_leftₓ
    ·
      apply le_reflₓ

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : ℕ) :
  padicNorm p (f (stationary_point hf)) = padicNorm p (f (max v1 (max (stationary_point hf) v3))) :=
  by 
    apply stationary_point_spec hf
    ·
      apply le_transₓ
      ·
        apply le_max_leftₓ _ v3
      ·
        apply le_max_rightₓ
    ·
      apply le_reflₓ

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : ℕ) :
  padicNorm p (f (stationary_point hf)) = padicNorm p (f (max v1 (max v2 (stationary_point hf)))) :=
  by 
    apply stationary_point_spec hf
    ·
      apply le_transₓ
      ·
        apply le_max_rightₓ v2
      ·
        apply le_max_rightₓ
    ·
      apply le_reflₓ

end Embedding

section Valuation

open CauSeq

variable {p : ℕ} [Fact p.prime]

/-! ### Valuation on `padic_seq` -/


/--
The `p`-adic valuation on `ℚ` lifts to `padic_seq p`.
`valuation f` is defined to be the valuation of the (`ℚ`-valued) stationary point of `f`.
-/
def Valuation (f : PadicSeq p) : ℤ :=
  if hf : f ≈ 0 then 0 else padicValRat p (f (stationary_point hf))

theorem norm_eq_pow_val {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm = (p^(-f.valuation : ℤ)) :=
  by 
    rw [norm, Valuation, dif_neg hf, dif_neg hf, padicNorm, if_neg]
    intro H 
    apply CauSeq.not_lim_zero_of_not_congr_zero hf 
    intro ε hε 
    use stationary_point hf 
    intro n hn 
    rw [stationary_point_spec hf (le_reflₓ _) hn]
    simpa [H] using hε

theorem val_eq_iff_norm_eq {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) :
  f.valuation = g.valuation ↔ f.norm = g.norm :=
  by 
    rw [norm_eq_pow_val hf, norm_eq_pow_val hg, ←neg_inj, zpow_inj]
    ·
      exactModCast (Fact.out p.prime).Pos
    ·
      exactModCast (Fact.out p.prime).ne_one

end Valuation

end PadicSeq

section 

open PadicSeq

private unsafe def index_simp_core (hh hf hg : expr) (at_ : Interactive.Loc := Interactive.Loc.ns [none]) :
  tactic Unit :=
  do 
    let [v1, v2, v3] ← [hh, hf, hg].mmap fun n => tactic.mk_app `` stationary_point [n] <|> return n 
    let e1 ← tactic.mk_app `` lift_index_left_left [hh, v2, v3] <|> return (quote.1 True)
    let e2 ← tactic.mk_app `` lift_index_left [hf, v1, v3] <|> return (quote.1 True)
    let e3 ← tactic.mk_app `` lift_index_right [hg, v1, v2] <|> return (quote.1 True)
    let sl ← [e1, e2, e3].mfoldl (fun s e => simp_lemmas.add s e) simp_lemmas.mk 
    when at_.include_goal (tactic.simp_target sl >> tactic.skip)
    let hs ← at_.get_locals 
    hs.mmap' (tactic.simp_hyp sl [])

/--
  This is a special-purpose tactic that lifts padic_norm (f (stationary_point f)) to
  padic_norm (f (max _ _ _)).
-/
unsafe def tactic.interactive.padic_index_simp (l : interactive.parse interactive.types.pexpr_list)
  (at_ : interactive.parse interactive.types.location) : tactic Unit :=
  do 
    let [h, f, g] ← l.mmap tactic.i_to_expr 
    index_simp_core h f g at_

end 

namespace PadicSeq

section Embedding

open CauSeq

variable {p : ℕ} [hp : Fact p.prime]

include hp

theorem norm_mul (f g : PadicSeq p) : (f*g).norm = f.norm*g.norm :=
  if hf : f ≈ 0 then
    have hg : (f*g) ≈ 0 := mul_equiv_zero' _ hf 
    by 
      simp only [hf, hg, norm, dif_pos, zero_mul]
  else
    if hg : g ≈ 0 then
      have hf : (f*g) ≈ 0 := mul_equiv_zero _ hg 
      by 
        simp only [hf, hg, norm, dif_pos, mul_zero]
    else
      have hfg : ¬(f*g) ≈ 0 :=
        by 
          apply mul_not_equiv_zero <;> assumption 
      by 
        unfold norm 
        splitIfs 
        padicIndexSimp [hfg, hf, hg]
        apply padicNorm.mul

theorem eq_zero_iff_equiv_zero (f : PadicSeq p) : mk f = 0 ↔ f ≈ 0 :=
  mk_eq

theorem ne_zero_iff_nequiv_zero (f : PadicSeq p) : mk f ≠ 0 ↔ ¬f ≈ 0 :=
  not_iff_not.2 (eq_zero_iff_equiv_zero _)

theorem norm_const (q : ℚ) : norm (const (padicNorm p) q) = padicNorm p q :=
  if hq : q = 0 then
    have  : const (padicNorm p) q ≈ 0 :=
      by 
        simp [hq] <;> apply Setoidₓ.refl (const (padicNorm p) 0)
    by 
      subst hq <;> simp [norm, this]
  else
    have  : ¬const (padicNorm p) q ≈ 0 := not_equiv_zero_const_of_nonzero hq 
    by 
      simp [norm, this]

theorem norm_values_discrete (a : PadicSeq p) (ha : ¬a ≈ 0) : ∃ z : ℤ, a.norm = («expr↑ » p^-z) :=
  let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha 
  by 
    simpa [hk] using padicNorm.values_discrete p hk'

theorem norm_one : norm (1 : PadicSeq p) = 1 :=
  have h1 : ¬(1 : PadicSeq p) ≈ 0 := one_not_equiv_zero _ 
  by 
    simp [h1, norm, hp.1.one_lt]

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem norm_eq_of_equiv_aux
{f g : padic_seq p}
(hf : «expr¬ »(«expr ≈ »(f, 0)))
(hg : «expr¬ »(«expr ≈ »(g, 0)))
(hfg : «expr ≈ »(f, g))
(h : «expr ≠ »(padic_norm p (f (stationary_point hf)), padic_norm p (g (stationary_point hg))))
(hlt : «expr < »(padic_norm p (g (stationary_point hg)), padic_norm p (f (stationary_point hf)))) : false :=
begin
  have [ident hpn] [":", expr «expr < »(0, «expr - »(padic_norm p (f (stationary_point hf)), padic_norm p (g (stationary_point hg))))] [],
  from [expr sub_pos_of_lt hlt],
  cases [expr hfg _ hpn] ["with", ident N, ident hN],
  let [ident i] [] [":=", expr max N (max (stationary_point hf) (stationary_point hg))],
  have [ident hi] [":", expr «expr ≤ »(N, i)] [],
  from [expr le_max_left _ _],
  have [ident hN'] [] [":=", expr hN _ hi],
  padic_index_simp ["[", expr N, ",", expr hf, ",", expr hg, "]"] ["at", ident hN', ident h, ident hlt],
  have [ident hpne] [":", expr «expr ≠ »(padic_norm p (f i), padic_norm p «expr- »(g i))] [],
  by rwa ["[", "<-", expr padic_norm.neg p (g i), "]"] ["at", ident h],
  let [ident hpnem] [] [":=", expr add_eq_max_of_ne p hpne],
  have [ident hpeq] [":", expr «expr = »(padic_norm p («expr - »(f, g) i), max (padic_norm p (f i)) (padic_norm p (g i)))] [],
  { rwa [expr padic_norm.neg] ["at", ident hpnem] },
  rw ["[", expr hpeq, ",", expr max_eq_left_of_lt hlt, "]"] ["at", ident hN'],
  have [] [":", expr «expr < »(padic_norm p (f i), padic_norm p (f i))] [],
  { apply [expr lt_of_lt_of_le hN'],
    apply [expr sub_le_self],
    apply [expr padic_norm.nonneg] },
  exact [expr lt_irrefl _ this]
end

private theorem norm_eq_of_equiv {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g) :
  padicNorm p (f (stationary_point hf)) = padicNorm p (g (stationary_point hg)) :=
  by 
    byContra h 
    cases' Decidable.em (padicNorm p (g (stationary_point hg)) < padicNorm p (f (stationary_point hf))) with hlt hnlt
    ·
      exact norm_eq_of_equiv_aux hf hg hfg h hlt
    ·
      apply norm_eq_of_equiv_aux hg hf (Setoidₓ.symm hfg) (Ne.symm h)
      apply lt_of_le_of_neₓ 
      apply le_of_not_gtₓ hnlt 
      apply h

theorem norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.norm = g.norm :=
  if hf : f ≈ 0 then
    have hg : g ≈ 0 := Setoidₓ.trans (Setoidₓ.symm hfg) hf 
    by 
      simp [norm, hf, hg]
  else
    have hg : ¬g ≈ 0 := hf ∘ Setoidₓ.trans hfg 
    by 
      unfold norm <;> splitIfs <;> exact norm_eq_of_equiv hf hg hfg

private theorem norm_nonarchimedean_aux {f g : PadicSeq p} (hfg : ¬(f+g) ≈ 0) (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) :
  (f+g).norm ≤ max f.norm g.norm :=
  by 
    unfold norm 
    splitIfs 
    padicIndexSimp [hfg, hf, hg]
    apply padicNorm.nonarchimedean

theorem norm_nonarchimedean (f g : PadicSeq p) : (f+g).norm ≤ max f.norm g.norm :=
  if hfg : (f+g) ≈ 0 then
    have  : 0 ≤ max f.norm g.norm := le_max_of_le_left (norm_nonneg _)
    by 
      simpa only [hfg, norm, Ne.def, le_max_iff, CauSeq.add_apply, not_true, dif_pos]
  else
    if hf : f ≈ 0 then
      have hfg' : (f+g) ≈ g :=
        by 
          change lim_zero (f - 0) at hf 
          show lim_zero ((f+g) - g)
          ·
            simpa only [sub_zero, add_sub_cancel] using hf 
      have hcfg : (f+g).norm = g.norm := norm_equiv hfg' 
      have hcl : f.norm = 0 := (norm_zero_iff f).2 hf 
      have  : max f.norm g.norm = g.norm :=
        by 
          rw [hcl] <;> exact max_eq_rightₓ (norm_nonneg _)
      by 
        rw [this, hcfg]
    else
      if hg : g ≈ 0 then
        have hfg' : (f+g) ≈ f :=
          by 
            change lim_zero (g - 0) at hg 
            show lim_zero ((f+g) - f)
            ·
              simpa only [add_sub_cancel', sub_zero] using hg 
        have hcfg : (f+g).norm = f.norm := norm_equiv hfg' 
        have hcl : g.norm = 0 := (norm_zero_iff g).2 hg 
        have  : max f.norm g.norm = f.norm :=
          by 
            rw [hcl] <;> exact max_eq_leftₓ (norm_nonneg _)
        by 
          rw [this, hcfg]
      else norm_nonarchimedean_aux hfg hf hg

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_eq
{f g : padic_seq p}
(h : ∀ k, «expr = »(padic_norm p (f k), padic_norm p (g k))) : «expr = »(f.norm, g.norm) :=
if hf : «expr ≈ »(f, 0) then have hg : «expr ≈ »(g, 0), from equiv_zero_of_val_eq_of_equiv_zero h hf,
by simp [] [] ["only"] ["[", expr hf, ",", expr hg, ",", expr norm, ",", expr dif_pos, "]"] [] [] else have hg : «expr¬ »(«expr ≈ »(g, 0)), from λ
hg, «expr $ »(hf, equiv_zero_of_val_eq_of_equiv_zero (by simp [] [] ["only"] ["[", expr h, ",", expr forall_const, ",", expr eq_self_iff_true, "]"] [] []) hg),
begin
  simp [] [] ["only"] ["[", expr hg, ",", expr hf, ",", expr norm, ",", expr dif_neg, ",", expr not_false_iff, "]"] [] [],
  let [ident i] [] [":=", expr max (stationary_point hf) (stationary_point hg)],
  have [ident hpf] [":", expr «expr = »(padic_norm p (f (stationary_point hf)), padic_norm p (f i))] [],
  { apply [expr stationary_point_spec],
    apply [expr le_max_left],
    apply [expr le_refl] },
  have [ident hpg] [":", expr «expr = »(padic_norm p (g (stationary_point hg)), padic_norm p (g i))] [],
  { apply [expr stationary_point_spec],
    apply [expr le_max_right],
    apply [expr le_refl] },
  rw ["[", expr hpf, ",", expr hpg, ",", expr h, "]"] []
end

theorem norm_neg (a : PadicSeq p) : (-a).norm = a.norm :=
  norm_eq$
    by 
      simp 

theorem norm_eq_of_add_equiv_zero {f g : PadicSeq p} (h : (f+g) ≈ 0) : f.norm = g.norm :=
  have  : lim_zero ((f+g) - 0) := h 
  have  : f ≈ -g :=
    show lim_zero (f - -g)by 
      simpa only [sub_zero, sub_neg_eq_add]
  have  : f.norm = (-g).norm := norm_equiv this 
  by 
    simpa only [norm_neg] using this

theorem add_eq_max_of_ne {f g : PadicSeq p} (hfgne : f.norm ≠ g.norm) : (f+g).norm = max f.norm g.norm :=
  have hfg : ¬(f+g) ≈ 0 := mt norm_eq_of_add_equiv_zero hfgne 
  if hf : f ≈ 0 then
    have  : lim_zero (f - 0) := hf 
    have  : (f+g) ≈ g :=
      show lim_zero ((f+g) - g)by 
        simpa only [sub_zero, add_sub_cancel]
    have h1 : (f+g).norm = g.norm := norm_equiv this 
    have h2 : f.norm = 0 := (norm_zero_iff _).2 hf 
    by 
      rw [h1, h2] <;> rw [max_eq_rightₓ (norm_nonneg _)]
  else
    if hg : g ≈ 0 then
      have  : lim_zero (g - 0) := hg 
      have  : (f+g) ≈ f :=
        show lim_zero ((f+g) - f)by 
          rw [add_sub_cancel'] <;> simpa only [sub_zero]
      have h1 : (f+g).norm = f.norm := norm_equiv this 
      have h2 : g.norm = 0 := (norm_zero_iff _).2 hg 
      by 
        rw [h1, h2] <;> rw [max_eq_leftₓ (norm_nonneg _)]
    else
      by 
        unfold norm  at hfgne⊢
        splitIfs  at hfgne⊢
        padicIndexSimp [hfg, hf, hg]  at hfgne⊢
        exact padicNorm.add_eq_max_of_ne p hfgne

end Embedding

end PadicSeq

/-- The p-adic numbers `Q_[p]` are the Cauchy completion of `ℚ` with respect to the p-adic norm. -/
def Padic (p : ℕ) [Fact p.prime] :=
  @CauSeq.Completion.Cauchy _ _ _ _ (padicNorm p) _

notation "ℚ_[" p "]" => Padic p

namespace Padic

section Completion

variable {p : ℕ} [Fact p.prime]

/-- The discrete field structure on `ℚ_p` is inherited from the Cauchy completion construction. -/
instance Field : Field ℚ_[p] :=
  CauSeq.Completion.field

instance : Inhabited ℚ_[p] :=
  ⟨0⟩

instance : HasZero ℚ_[p] :=
  by 
    infer_instance

instance : HasOne ℚ_[p] :=
  by 
    infer_instance

instance : Add ℚ_[p] :=
  by 
    infer_instance

instance : Mul ℚ_[p] :=
  by 
    infer_instance

instance : Sub ℚ_[p] :=
  by 
    infer_instance

instance : Neg ℚ_[p] :=
  by 
    infer_instance

instance : Div ℚ_[p] :=
  by 
    infer_instance

instance : AddCommGroupₓ ℚ_[p] :=
  by 
    infer_instance

instance : CommRingₓ ℚ_[p] :=
  by 
    infer_instance

/-- Builds the equivalence class of a Cauchy sequence of rationals. -/
def mk : PadicSeq p → ℚ_[p] :=
  Quotientₓ.mk

end Completion

section Completion

variable (p : ℕ) [Fact p.prime]

theorem mk_eq {f g : PadicSeq p} : mk f = mk g ↔ f ≈ g :=
  Quotientₓ.eq

/-- Embeds the rational numbers in the p-adic numbers. -/
def of_rat : ℚ → ℚ_[p] :=
  CauSeq.Completion.ofRat

@[simp]
theorem of_rat_add : ∀ x y : ℚ, of_rat p (x+y) = of_rat p x+of_rat p y :=
  CauSeq.Completion.of_rat_add

@[simp]
theorem of_rat_neg : ∀ x : ℚ, of_rat p (-x) = -of_rat p x :=
  CauSeq.Completion.of_rat_neg

@[simp]
theorem of_rat_mul : ∀ x y : ℚ, of_rat p (x*y) = of_rat p x*of_rat p y :=
  CauSeq.Completion.of_rat_mul

@[simp]
theorem of_rat_sub : ∀ x y : ℚ, of_rat p (x - y) = of_rat p x - of_rat p y :=
  CauSeq.Completion.of_rat_sub

@[simp]
theorem of_rat_div : ∀ x y : ℚ, of_rat p (x / y) = of_rat p x / of_rat p y :=
  CauSeq.Completion.of_rat_div

@[simp]
theorem of_rat_one : of_rat p 1 = 1 :=
  rfl

@[simp]
theorem of_rat_zero : of_rat p 0 = 0 :=
  rfl

theorem cast_eq_of_rat_of_nat (n : ℕ) : («expr↑ » n : ℚ_[p]) = of_rat p n :=
  by 
    induction' n with n ih
    ·
      rfl
    ·
      simpa using ih

theorem cast_eq_of_rat_of_int (n : ℤ) : «expr↑ » n = of_rat p n :=
  by 
    induction n <;> simp [cast_eq_of_rat_of_nat]

theorem cast_eq_of_rat : ∀ q : ℚ, («expr↑ » q : ℚ_[p]) = of_rat p q
| ⟨n, d, h1, h2⟩ =>
  show «expr↑ » n / «expr↑ » d = _ from
    have  : (⟨n, d, h1, h2⟩ : ℚ) = Rat.mk n d := Rat.num_denom' 
    by 
      simp [this, Rat.mk_eq_div, of_rat_div, cast_eq_of_rat_of_int, cast_eq_of_rat_of_nat]

@[normCast]
theorem coe_add : ∀ {x y : ℚ}, («expr↑ » (x+y) : ℚ_[p]) = «expr↑ » x+«expr↑ » y :=
  by 
    simp [cast_eq_of_rat]

@[normCast]
theorem coe_neg : ∀ {x : ℚ}, («expr↑ » (-x) : ℚ_[p]) = -«expr↑ » x :=
  by 
    simp [cast_eq_of_rat]

@[normCast]
theorem coe_mul : ∀ {x y : ℚ}, («expr↑ » (x*y) : ℚ_[p]) = «expr↑ » x*«expr↑ » y :=
  by 
    simp [cast_eq_of_rat]

@[normCast]
theorem coe_sub : ∀ {x y : ℚ}, («expr↑ » (x - y) : ℚ_[p]) = «expr↑ » x - «expr↑ » y :=
  by 
    simp [cast_eq_of_rat]

@[normCast]
theorem coe_div : ∀ {x y : ℚ}, («expr↑ » (x / y) : ℚ_[p]) = «expr↑ » x / «expr↑ » y :=
  by 
    simp [cast_eq_of_rat]

@[normCast]
theorem coe_one : («expr↑ » 1 : ℚ_[p]) = 1 :=
  by 
    simp [cast_eq_of_rat]

@[normCast]
theorem coe_zero : («expr↑ » 0 : ℚ_[p]) = 0 :=
  rfl

theorem const_equiv {q r : ℚ} : const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r :=
  ⟨fun heq : lim_zero (const (padicNorm p) (q - r)) => eq_of_sub_eq_zero$ const_lim_zero.1 HEq,
    fun heq =>
      by 
        rw [HEq] <;> apply Setoidₓ.refl _⟩

theorem of_rat_eq {q r : ℚ} : of_rat p q = of_rat p r ↔ q = r :=
  ⟨(const_equiv p).1 ∘ Quotientₓ.eq.1,
    fun h =>
      by 
        rw [h]⟩

@[normCast]
theorem coe_inj {q r : ℚ} : («expr↑ » q : ℚ_[p]) = «expr↑ » r ↔ q = r :=
  by 
    simp [cast_eq_of_rat, of_rat_eq]

instance : CharZero ℚ_[p] :=
  ⟨fun m n =>
      by 
        rw [←Rat.cast_coe_nat]
        normCast 
        exact id⟩

end Completion

end Padic

/-- The rational-valued p-adic norm on `ℚ_p` is lifted from the norm on Cauchy sequences. The
canonical form of this function is the normed space instance, with notation `∥ ∥`. -/
def padicNormE {p : ℕ} [hp : Fact p.prime] : ℚ_[p] → ℚ :=
  Quotientₓ.lift PadicSeq.norm$ @PadicSeq.norm_equiv _ _

namespace padicNormE

section Embedding

open PadicSeq

variable {p : ℕ} [Fact p.prime]

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem defn
(f : padic_seq p)
{ε : exprℚ()}
(hε : «expr < »(0, ε)) : «expr∃ , »((N), ∀ i «expr ≥ » N, «expr < »(padic_norm_e «expr - »(«expr⟦ ⟧»(f), f i), ε)) :=
begin
  simp [] [] ["only"] ["[", expr padic.cast_eq_of_rat, "]"] [] [],
  change [expr «expr∃ , »((N), ∀ i «expr ≥ » N, «expr < »(«expr - »(f, const _ (f i)).norm, ε))] [] [],
  by_contradiction [ident h],
  cases [expr cauchy₂ f hε] ["with", ident N, ident hN],
  have [] [":", expr ∀ N, «expr∃ , »((i «expr ≥ » N), «expr ≤ »(ε, «expr - »(f, const _ (f i)).norm))] [],
  by simpa [] [] ["only"] ["[", expr not_forall, ",", expr not_exists, ",", expr not_lt, "]"] [] ["using", expr h],
  rcases [expr this N, "with", "⟨", ident i, ",", ident hi, ",", ident hge, "⟩"],
  have [ident hne] [":", expr «expr¬ »(«expr ≈ »(«expr - »(f, const (padic_norm p) (f i)), 0))] [],
  { intro [ident h],
    unfold [ident padic_seq.norm] ["at", ident hge]; split_ifs ["at", ident hge] [],
    exact [expr not_lt_of_ge hge hε] },
  unfold [ident padic_seq.norm] ["at", ident hge]; split_ifs ["at", ident hge] [],
  apply [expr not_le_of_gt _ hge],
  cases [expr decidable.em «expr ≤ »(N, stationary_point hne)] ["with", ident hgen, ident hngen],
  { apply [expr hN]; assumption },
  { have [] [] [":=", expr stationary_point_spec hne (le_refl _) (le_of_not_le hngen)],
    rw ["<-", expr this] [],
    apply [expr hN],
    apply [expr le_refl],
    assumption }
end

protected theorem nonneg (q : ℚ_[p]) : 0 ≤ padicNormE q :=
  Quotientₓ.induction_on q$ norm_nonneg

theorem zero_def : (0 : ℚ_[p]) = «expr⟦ ⟧» 0 :=
  rfl

theorem zero_iff (q : ℚ_[p]) : padicNormE q = 0 ↔ q = 0 :=
  Quotientₓ.induction_on q$
    by 
      simpa only [zero_def, Quotientₓ.eq] using norm_zero_iff

@[simp]
protected theorem zero : padicNormE (0 : ℚ_[p]) = 0 :=
  (zero_iff _).2 rfl

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
@[simp]
protected theorem one' : padicNormE (1 : ℚ_[p]) = 1 :=
  norm_one

@[simp]
protected theorem neg (q : ℚ_[p]) : padicNormE (-q) = padicNormE q :=
  Quotientₓ.induction_on q$ norm_neg

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
theorem nonarchimedean' (q r : ℚ_[p]) : padicNormE (q+r) ≤ max (padicNormE q) (padicNormE r) :=
  Quotientₓ.induction_on₂ q r$ norm_nonarchimedean

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
theorem add_eq_max_of_ne' {q r : ℚ_[p]} :
  padicNormE q ≠ padicNormE r → padicNormE (q+r) = max (padicNormE q) (padicNormE r) :=
  Quotientₓ.induction_on₂ q r$ fun _ _ => PadicSeq.add_eq_max_of_ne

theorem triangle_ineq (x y z : ℚ_[p]) : padicNormE (x - z) ≤ padicNormE (x - y)+padicNormE (y - z) :=
  calc padicNormE (x - z) = padicNormE ((x - y)+y - z) :=
    by 
      rw [sub_add_sub_cancel]
    _ ≤ max (padicNormE (x - y)) (padicNormE (y - z)) := padicNormE.nonarchimedean' _ _ 
    _ ≤ padicNormE (x - y)+padicNormE (y - z) := max_le_add_of_nonneg (padicNormE.nonneg _) (padicNormE.nonneg _)
    

protected theorem add (q r : ℚ_[p]) : padicNormE (q+r) ≤ padicNormE q+padicNormE r :=
  calc padicNormE (q+r) ≤ max (padicNormE q) (padicNormE r) := nonarchimedean' _ _ 
    _ ≤ padicNormE q+padicNormE r := max_le_add_of_nonneg (padicNormE.nonneg _) (padicNormE.nonneg _)
    

protected theorem mul' (q r : ℚ_[p]) : padicNormE (q*r) = padicNormE q*padicNormE r :=
  Quotientₓ.induction_on₂ q r$ norm_mul

instance : IsAbsoluteValue (@padicNormE p _) :=
  { abv_nonneg := padicNormE.nonneg, abv_eq_zero := zero_iff, abv_add := padicNormE.add, abv_mul := padicNormE.mul' }

@[simp]
theorem eq_padic_norm' (q : ℚ) : padicNormE (Padic.ofRat p q) = padicNorm p q :=
  norm_const _

protected theorem image' {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, padicNormE q = (p^-n) :=
  Quotientₓ.induction_on q$
    fun f hf =>
      have  : ¬f ≈ 0 := (ne_zero_iff_nequiv_zero f).1 hf 
      norm_values_discrete f this

theorem sub_rev (q r : ℚ_[p]) : padicNormE (q - r) = padicNormE (r - q) :=
  by 
    rw [←padicNormE.neg] <;> simp 

end Embedding

end padicNormE

namespace Padic

section Complete

open PadicSeq Padic

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rat_dense'
{p : exprℕ()}
[fact p.prime]
(q : «exprℚ_[ ]»(p))
{ε : exprℚ()}
(hε : «expr < »(0, ε)) : «expr∃ , »((r : exprℚ()), «expr < »(padic_norm_e «expr - »(q, r), ε)) :=
«expr $ »(quotient.induction_on q, λ
 q', have «expr∃ , »((N), ∀ m n «expr ≥ » N, «expr < »(padic_norm p «expr - »(q' m, q' n), ε)), from cauchy₂ _ hε,
 let ⟨N, hN⟩ := this in
 ⟨q' N, begin
    simp [] [] ["only"] ["[", expr padic.cast_eq_of_rat, "]"] [] [],
    change [expr «expr < »(padic_seq.norm «expr - »(q', const _ (q' N)), ε)] [] [],
    cases [expr decidable.em «expr ≈ »(«expr - »(q', const (padic_norm p) (q' N)), 0)] ["with", ident heq, ident hne'],
    { simpa [] [] ["only"] ["[", expr heq, ",", expr padic_seq.norm, ",", expr dif_pos, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr padic_seq.norm, ",", expr dif_neg hne', "]"] [] [],
      change [expr «expr < »(padic_norm p «expr - »(q' _, q' _), ε)] [] [],
      have [] [] [":=", expr stationary_point_spec hne'],
      cases [expr decidable.em «expr ≤ »(stationary_point hne', N)] ["with", ident hle, ident hle],
      { have [] [] [":=", expr eq.symm (this (le_refl _) hle)],
        simp [] [] ["only"] ["[", expr const_apply, ",", expr sub_apply, ",", expr padic_norm.zero, ",", expr sub_self, "]"] [] ["at", ident this],
        simpa [] [] ["only"] ["[", expr this, "]"] [] [] },
      { apply [expr hN],
        apply [expr le_of_lt],
        apply [expr lt_of_not_ge],
        apply [expr hle],
        apply [expr le_refl] } }
  end⟩)

variable {p : ℕ} [Fact p.prime] (f : CauSeq _ (@padicNormE p _))

open Classical

private theorem div_nat_pos (n : ℕ) : 0 < 1 / (n+1 : ℚ) :=
  div_pos zero_lt_one
    (by 
      exactModCast succ_pos _)

/-- `lim_seq f`, for `f` a Cauchy sequence of `p`-adic numbers,
is a sequence of rationals with the same limit point as `f`. -/
def lim_seq : ℕ → ℚ :=
  fun n => Classical.some (rat_dense' (f n) (div_nat_pos n))

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exi_rat_seq_conv
{ε : exprℚ()}
(hε : «expr < »(0, ε)) : «expr∃ , »((N), ∀
 i «expr ≥ » N, «expr < »(padic_norm_e «expr - »(f i, (lim_seq f i : «exprℚ_[ ]»(p))), ε)) :=
begin
  refine [expr (exists_nat_gt «expr / »(1, ε)).imp (λ N hN i hi, _)],
  have [ident h] [] [":=", expr classical.some_spec (rat_dense' (f i) (div_nat_pos i))],
  refine [expr lt_of_lt_of_le h («expr $ »(div_le_iff', by exact_mod_cast [expr succ_pos _]).mpr _)],
  rw [expr right_distrib] [],
  apply [expr le_add_of_le_of_nonneg],
  { exact [expr (div_le_iff hε).mp (le_trans (le_of_lt hN) (by exact_mod_cast [expr hi]))] },
  { apply [expr le_of_lt],
    simpa [] [] [] [] [] [] }
end

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exi_rat_seq_conv_cauchy : is_cau_seq (padic_norm p) (lim_seq f) :=
assume ε hε, have hε3 : «expr < »(0, «expr / »(ε, 3)), from div_pos hε (by norm_num [] []),
let ⟨N, hN⟩ := exi_rat_seq_conv f hε3, ⟨N2, hN2⟩ := f.cauchy₂ hε3 in
begin
  existsi [expr max N N2],
  intros [ident j, ident hj],
  suffices [] [":", expr «expr < »(padic_norm_e «expr + »(«expr - »(«expr↑ »(lim_seq f j), f (max N N2)), «expr - »(f (max N N2), lim_seq f (max N N2))), ε)],
  { ring_nf [] [] ["at", ident this, "⊢"],
    rw ["[", "<-", expr padic_norm_e.eq_padic_norm', ",", "<-", expr padic.cast_eq_of_rat, "]"] [],
    exact_mod_cast [expr this] },
  { apply [expr lt_of_le_of_lt],
    { apply [expr padic_norm_e.add] },
    { have [] [":", expr «expr ≠ »((3 : exprℚ()), 0)] [],
      by norm_num [] [],
      have [] [":", expr «expr = »(ε, «expr + »(«expr + »(«expr / »(ε, 3), «expr / »(ε, 3)), «expr / »(ε, 3)))] [],
      { field_simp [] ["[", expr this, "]"] [] [],
        simp [] [] ["only"] ["[", expr bit0, ",", expr bit1, ",", expr mul_add, ",", expr mul_one, "]"] [] [] },
      rw [expr this] [],
      apply [expr add_lt_add],
      { suffices [] [":", expr «expr < »(padic_norm_e «expr + »(«expr - »(«expr↑ »(lim_seq f j), f j), «expr - »(f j, f (max N N2))), «expr + »(«expr / »(ε, 3), «expr / »(ε, 3)))],
        by simpa [] [] ["only"] ["[", expr sub_add_sub_cancel, "]"] [] [],
        apply [expr lt_of_le_of_lt],
        { apply [expr padic_norm_e.add] },
        { apply [expr add_lt_add],
          { rw ["[", expr padic_norm_e.sub_rev, "]"] [],
            apply_mod_cast [expr hN],
            exact [expr le_of_max_le_left hj] },
          { apply [expr hN2],
            exact [expr le_of_max_le_right hj],
            apply [expr le_max_right] } } },
      { apply_mod_cast [expr hN],
        apply [expr le_max_left] } } }
end

private def lim' : PadicSeq p :=
  ⟨_, exi_rat_seq_conv_cauchy f⟩

private def limₓ : ℚ_[p] :=
  «expr⟦ ⟧» (lim' f)

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem complete' : «expr∃ , »((q : «exprℚ_[ ]»(p)), ∀
 ε «expr > » 0, «expr∃ , »((N), ∀ i «expr ≥ » N, «expr < »(padic_norm_e «expr - »(q, f i), ε))) :=
⟨lim f, λ
 ε
 hε, let ⟨N, hN⟩ := exi_rat_seq_conv f (show «expr < »(0, «expr / »(ε, 2)), from div_pos hε (by norm_num [] [])),
     ⟨N2, hN2⟩ := padic_norm_e.defn (lim' f) (show «expr < »(0, «expr / »(ε, 2)), from div_pos hε (by norm_num [] [])) in
 begin
   existsi [expr max N N2],
   intros [ident i, ident hi],
   suffices [] [":", expr «expr < »(padic_norm_e «expr + »(«expr - »(lim f, lim' f i), «expr - »(lim' f i, f i)), ε)],
   { ring_nf [] [] ["at", ident this]; exact [expr this] },
   { apply [expr lt_of_le_of_lt],
     { apply [expr padic_norm_e.add] },
     { have [] [":", expr «expr = »(ε, «expr + »(«expr / »(ε, 2), «expr / »(ε, 2)))] [],
       by rw ["<-", expr add_self_div_two ε] []; simp [] [] [] [] [] [],
       rw [expr this] [],
       apply [expr add_lt_add],
       { apply [expr hN2],
         exact [expr le_of_max_le_right hi] },
       { rw_mod_cast ["[", expr padic_norm_e.sub_rev, "]"] [],
         apply [expr hN],
         exact [expr le_of_max_le_left hi] } } }
 end⟩

end Complete

section NormedSpace

variable (p : ℕ) [Fact p.prime]

instance : HasDist ℚ_[p] :=
  ⟨fun x y => padicNormE (x - y)⟩

instance : MetricSpace ℚ_[p] :=
  { dist_self :=
      by 
        simp [dist],
    dist_comm :=
      fun x y =>
        by 
          unfold dist <;> rw [←padicNormE.neg (x - y)] <;> simp ,
    dist_triangle :=
      by 
        intros 
        unfold dist 
        exactModCast padicNormE.triangle_ineq _ _ _,
    eq_of_dist_eq_zero :=
      by 
        unfold dist 
        intro _ _ h 
        apply eq_of_sub_eq_zero 
        apply (padicNormE.zero_iff _).1 
        exactModCast h }

instance : HasNorm ℚ_[p] :=
  ⟨fun x => padicNormE x⟩

instance : NormedField ℚ_[p] :=
  { dist_eq := fun _ _ => rfl,
    norm_mul' :=
      by 
        simp [HasNorm.norm, padicNormE.mul'] }

instance IsAbsoluteValue : IsAbsoluteValue fun a : ℚ_[p] => ∥a∥ :=
  { abv_nonneg := norm_nonneg, abv_eq_zero := fun _ => norm_eq_zero, abv_add := norm_add_le,
    abv_mul :=
      by 
        simp [HasNorm.norm, padicNormE.mul'] }

theorem rat_dense {p : ℕ} {hp : Fact p.prime} (q : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) : ∃ r : ℚ, ∥q - r∥ < ε :=
  let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε 
  let ⟨r, hr⟩ :=
    rat_dense' q
      (by 
        simpa using hε'l)
  ⟨r,
    lt_transₓ
      (by 
        simpa [HasNorm.norm] using hr)
      hε'r⟩

end NormedSpace

end Padic

namespace padicNormE

section NormedSpace

variable {p : ℕ} [hp : Fact p.prime]

include hp

@[simp]
protected theorem mul (q r : ℚ_[p]) : ∥q*r∥ = ∥q∥*∥r∥ :=
  by 
    simp [HasNorm.norm, padicNormE.mul']

protected theorem is_norm (q : ℚ_[p]) : «expr↑ » (padicNormE q) = ∥q∥ :=
  rfl

theorem nonarchimedean (q r : ℚ_[p]) : ∥q+r∥ ≤ max ∥q∥ ∥r∥ :=
  by 
    unfold HasNorm.norm 
    exactModCast nonarchimedean' _ _

theorem add_eq_max_of_ne {q r : ℚ_[p]} (h : ∥q∥ ≠ ∥r∥) : ∥q+r∥ = max ∥q∥ ∥r∥ :=
  by 
    unfold HasNorm.norm 
    applyModCast add_eq_max_of_ne' 
    intro h' 
    apply h 
    unfold HasNorm.norm 
    exactModCast h'

@[simp]
theorem eq_padic_norm (q : ℚ) : ∥(«expr↑ » q : ℚ_[p])∥ = padicNorm p q :=
  by 
    unfold HasNorm.norm 
    rw [←padicNormE.eq_padic_norm', ←Padic.cast_eq_of_rat]

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem norm_p : «expr = »(«expr∥ ∥»((p : «exprℚ_[ ]»(p))), «expr ⁻¹»(p)) :=
begin
  have [ident p₀] [":", expr «expr ≠ »(p, 0)] [":=", expr hp.1.ne_zero],
  have [ident p₁] [":", expr «expr ≠ »(p, 1)] [":=", expr hp.1.ne_one],
  simp [] [] [] ["[", expr p₀, ",", expr p₁, ",", expr norm, ",", expr padic_norm, ",", expr padic_val_rat, ",", expr zpow_neg, ",", expr padic.cast_eq_of_rat_of_nat, "]"] [] []
end

theorem norm_p_lt_one : ∥(p : ℚ_[p])∥ < 1 :=
  by 
    rw [norm_p]
    apply inv_lt_one 
    exactModCast hp.1.one_lt

@[simp]
theorem norm_p_pow (n : ℤ) : ∥(p^n : ℚ_[p])∥ = (p^-n) :=
  by 
    rw [NormedField.norm_zpow, norm_p] <;> fieldSimp

instance : NondiscreteNormedField ℚ_[p] :=
  { non_trivial :=
      ⟨p⁻¹,
        by 
          rw [NormedField.norm_inv, norm_p, inv_inv₀]
          exactModCast hp.1.one_lt⟩ }

protected theorem image {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, ∥q∥ = «expr↑ » ((«expr↑ » p : ℚ)^-n) :=
  Quotientₓ.induction_on q$
    fun f hf =>
      have  : ¬f ≈ 0 := (PadicSeq.ne_zero_iff_nequiv_zero f).1 hf 
      let ⟨n, hn⟩ := PadicSeq.norm_values_discrete f this
      ⟨n, congr_argₓ coeₓ hn⟩

protected theorem is_rat (q : ℚ_[p]) : ∃ q' : ℚ, ∥q∥ = «expr↑ » q' :=
  if h : q = 0 then
    ⟨0,
      by 
        simp [h]⟩
  else
    let ⟨n, hn⟩ := padicNormE.image h
    ⟨_, hn⟩

/--`rat_norm q`, for a `p`-adic number `q` is the `p`-adic norm of `q`, as rational number.

The lemma `padic_norm_e.eq_rat_norm` asserts `∥q∥ = rat_norm q`. -/
def rat_norm (q : ℚ_[p]) : ℚ :=
  Classical.some (padicNormE.is_rat q)

theorem eq_rat_norm (q : ℚ_[p]) : ∥q∥ = rat_norm q :=
  Classical.some_spec (padicNormE.is_rat q)

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_rat_le_one : ∀
{q : exprℚ()}
(hq : «expr¬ »(«expr ∣ »(p, q.denom))), «expr ≤ »(«expr∥ ∥»((q : «exprℚ_[ ]»(p))), 1)
| ⟨n, d, hn, hd⟩ := λ
hq : «expr¬ »(«expr ∣ »(p, d)), if hnz : «expr = »(n, 0) then have «expr = »((⟨n, d, hn, hd⟩ : exprℚ()), 0), from rat.zero_iff_num_zero.mpr hnz,
by norm_num ["[", expr this, "]"] [] else begin
  have [ident hnz'] [":", expr «expr ≠ »({ rat . num := n, denom := d, pos := hn, cop := hd }, 0)] [],
  from [expr mt rat.zero_iff_num_zero.1 hnz],
  rw ["[", expr padic_norm_e.eq_padic_norm, "]"] [],
  norm_cast [],
  rw ["[", expr padic_norm.eq_zpow_of_nonzero p hnz', ",", expr padic_val_rat_def p hnz', "]"] [],
  have [ident h] [":", expr «expr = »((multiplicity p d).get _, 0)] [],
  by simp [] [] [] ["[", expr multiplicity_eq_zero_of_not_dvd, ",", expr hq, "]"] [] [],
  simp [] [] ["only"] [] [] [],
  norm_cast [],
  rw_mod_cast ["[", expr h, ",", expr sub_zero, "]"] [],
  apply [expr zpow_le_one_of_nonpos],
  { exact_mod_cast [expr le_of_lt hp.1.one_lt] },
  { apply [expr neg_nonpos_of_nonneg],
    norm_cast [],
    simp [] [] [] [] [] [] }
end

theorem norm_int_le_one (z : ℤ) : ∥(z : ℚ_[p])∥ ≤ 1 :=
  suffices ∥((z : ℚ) : ℚ_[p])∥ ≤ 1by 
    simpa 
  norm_rat_le_one$
    by 
      simp [hp.1.ne_one]

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ∥(k : ℚ_[p])∥ < 1 ↔ «expr↑ » p ∣ k :=
  by 
    split 
    ·
      intro h 
      contrapose! h 
      apply le_of_eqₓ 
      rw [eq_comm]
      calc ∥(k : ℚ_[p])∥ = ∥((k : ℚ) : ℚ_[p])∥ :=
        by 
          normCast _ = padicNorm p k :=
        padicNormE.eq_padic_norm _ _ = 1 := _ 
      rw [padicNorm]
      splitIfs with H
      ·
        exfalso 
        apply h 
        normCast  at H 
        rw [H]
        apply dvd_zero
      ·
        normCast  at H⊢
        convert zpow_zero _ 
        simp only [neg_eq_zero]
        rw [padicValRat.padic_val_rat_of_int _ hp.1.ne_one H]
        normCast 
        rw [←Enat.coe_inj, Enat.coe_get, Nat.cast_zero]
        apply multiplicity.multiplicity_eq_zero_of_not_dvd h
    ·
      rintro ⟨x, rfl⟩
      pushCast 
      rw [padicNormE.mul]
      calc _ ≤ ∥(p : ℚ_[p])∥*1 :=
        mul_le_mul (le_reflₓ _)
          (by 
            simpa using norm_int_le_one _)
          (norm_nonneg _) (norm_nonneg _)_ < 1 :=
        _
      ·
        rw [mul_oneₓ, padicNormE.norm_p]
        apply inv_lt_one 
        exactModCast hp.1.one_lt

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_int_le_pow_iff_dvd
(k : exprℤ())
(n : exprℕ()) : «expr ↔ »(«expr ≤ »(«expr∥ ∥»((k : «exprℚ_[ ]»(p))), «expr ^ »(«expr↑ »(p), («expr- »(n) : exprℤ()))), «expr ∣ »(«expr↑ »(«expr ^ »(p, n)), k)) :=
begin
  have [] [":", expr «expr = »(«expr ^ »((p : exprℝ()), («expr- »(n) : exprℤ())), «expr↑ »((«expr ^ »(p, («expr- »(n) : exprℤ())) : exprℚ())))] [],
  { simp [] [] [] [] [] [] },
  rw ["[", expr show «expr = »((k : «exprℚ_[ ]»(p)), ((k : exprℚ()) : «exprℚ_[ ]»(p))), by norm_cast [], ",", expr eq_padic_norm, ",", expr this, "]"] [],
  norm_cast [],
  rw [expr padic_norm.dvd_iff_norm_le] []
end

theorem eq_of_norm_add_lt_right {p : ℕ} {hp : Fact p.prime} {z1 z2 : ℚ_[p]} (h : ∥z1+z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
  by_contradiction$
    fun hne =>
      not_lt_of_geₓ
        (by 
          rw [padicNormE.add_eq_max_of_ne hne] <;> apply le_max_rightₓ)
        h

theorem eq_of_norm_add_lt_left {p : ℕ} {hp : Fact p.prime} {z1 z2 : ℚ_[p]} (h : ∥z1+z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
  by_contradiction$
    fun hne =>
      not_lt_of_geₓ
        (by 
          rw [padicNormE.add_eq_max_of_ne hne] <;> apply le_max_leftₓ)
        h

end NormedSpace

end padicNormE

namespace Padic

variable {p : ℕ} [hp_prime : Fact p.prime]

include hp_prime

set_option eqn_compiler.zeta true

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance complete : cau_seq.is_complete «exprℚ_[ ]»(p) norm :=
begin
  split,
  intro [ident f],
  have [ident cau_seq_norm_e] [":", expr is_cau_seq padic_norm_e f] [],
  { intros [ident ε, ident hε],
    let [ident h] [] [":=", expr is_cau f ε (by exact_mod_cast [expr hε])],
    unfold [ident norm] ["at", ident h],
    apply_mod_cast [expr h] },
  cases [expr padic.complete' ⟨f, cau_seq_norm_e⟩] ["with", ident q, ident hq],
  existsi [expr q],
  intros [ident ε, ident hε],
  cases [expr exists_rat_btwn hε] ["with", ident ε', ident hε'],
  norm_cast ["at", ident hε'],
  cases [expr hq ε' hε'.1] ["with", ident N, ident hN],
  existsi [expr N],
  intros [ident i, ident hi],
  let [ident h] [] [":=", expr hN i hi],
  unfold [ident norm] [],
  rw_mod_cast ["[", expr cau_seq.sub_apply, ",", expr padic_norm_e.sub_rev, "]"] [],
  refine [expr lt_trans _ hε'.2],
  exact_mod_cast [expr hN i hi]
end

theorem padic_norm_e_lim_le {f : CauSeq ℚ_[p] norm} {a : ℝ} (ha : 0 < a) (hf : ∀ i, ∥f i∥ ≤ a) : ∥f.lim∥ ≤ a :=
  let ⟨N, hN⟩ := Setoidₓ.symm (CauSeq.equiv_lim f) _ ha 
  calc ∥f.lim∥ = ∥(f.lim - f N)+f N∥ :=
    by 
      simp 
    _ ≤ max ∥f.lim - f N∥ ∥f N∥ := padicNormE.nonarchimedean _ _ 
    _ ≤ a := max_leₓ (le_of_ltₓ (hN _ (le_reflₓ _))) (hf _)
    

/-!
### Valuation on `ℚ_[p]`
-/


-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
`padic.valuation` lifts the p-adic valuation on rationals to `ℚ_[p]`.
-/ def valuation : «exprℚ_[ ]»(p) → exprℤ() :=
quotient.lift (@padic_seq.valuation p _) (λ f g h, begin
   by_cases [expr hf, ":", expr «expr ≈ »(f, 0)],
   { have [ident hg] [":", expr «expr ≈ »(g, 0)] [],
     from [expr setoid.trans (setoid.symm h) hf],
     simp [] [] [] ["[", expr hf, ",", expr hg, ",", expr padic_seq.valuation, "]"] [] [] },
   { have [ident hg] [":", expr «expr¬ »(«expr ≈ »(g, 0))] [],
     from [expr λ hg, hf (setoid.trans h hg)],
     rw [expr padic_seq.val_eq_iff_norm_eq hf hg] [],
     exact [expr padic_seq.norm_equiv h] }
 end)

@[simp]
theorem valuation_zero : Valuation (0 : ℚ_[p]) = 0 :=
  dif_pos ((const_equiv p).2 rfl)

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem valuation_one : «expr = »(valuation (1 : «exprℚ_[ ]»(p)), 0) :=
begin
  change [expr «expr = »(dite «expr ≈ »(cau_seq.const (padic_norm p) 1, _) _ _, _)] [] [],
  have [ident h] [":", expr «expr¬ »(«expr ≈ »(cau_seq.const (padic_norm p) 1, 0))] [],
  { assume [binders (H)],
    erw [expr const_equiv p] ["at", ident H],
    exact [expr one_ne_zero H] },
  rw [expr dif_neg h] [],
  simp [] [] [] [] [] []
end

theorem norm_eq_pow_val {x : ℚ_[p]} : x ≠ 0 → ∥x∥ = (p^-x.valuation) :=
  by 
    apply Quotientₓ.induction_on' x 
    clear x 
    intro f hf 
    change (PadicSeq.norm _ : ℝ) = ((p : ℝ)^-PadicSeq.valuation _)
    rw [PadicSeq.norm_eq_pow_val]
    change «expr↑ » ((p : ℚ)^-PadicSeq.valuation f) = ((p : ℝ)^-PadicSeq.valuation f)
    ·
      rw [Rat.cast_zpow]
      congr 1
      normCast
    ·
      apply CauSeq.not_lim_zero_of_not_congr_zero 
      contrapose! hf 
      apply Quotientₓ.sound 
      simpa using hf

-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem valuation_p : «expr = »(valuation (p : «exprℚ_[ ]»(p)), 1) :=
begin
  have [ident h] [":", expr «expr < »((1 : exprℝ()), p)] [":=", expr by exact_mod_cast [expr (fact.out p.prime).one_lt]],
  rw ["<-", expr neg_inj] [],
  apply [expr (zpow_strict_mono h).injective],
  dsimp ["only"] [] [] [],
  rw ["<-", expr norm_eq_pow_val] [],
  { simp [] [] [] [] [] [] },
  { exact_mod_cast [expr (fact.out p.prime).ne_zero] }
end

section NormLeIff

/-! ### Various characterizations of open unit balls -/


-- error in NumberTheory.Padics.PadicNumbers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_le_pow_iff_norm_lt_pow_add_one
(x : «exprℚ_[ ]»(p))
(n : exprℤ()) : «expr ↔ »(«expr ≤ »(«expr∥ ∥»(x), «expr ^ »(p, n)), «expr < »(«expr∥ ∥»(x), «expr ^ »(p, «expr + »(n, 1)))) :=
begin
  have [ident aux] [":", expr ∀ n : exprℤ(), «expr < »(0, («expr ^ »(p, n) : exprℝ()))] [],
  { apply [expr nat.zpow_pos_of_pos],
    exact [expr hp_prime.1.pos] },
  by_cases [expr hx0, ":", expr «expr = »(x, 0)],
  { simp [] [] [] ["[", expr hx0, ",", expr norm_zero, ",", expr aux, ",", expr le_of_lt (aux _), "]"] [] [] },
  rw [expr norm_eq_pow_val hx0] [],
  have [ident h1p] [":", expr «expr < »(1, (p : exprℝ()))] [],
  { exact_mod_cast [expr hp_prime.1.one_lt] },
  have [ident H] [] [":=", expr zpow_strict_mono h1p],
  rw ["[", expr H.le_iff_le, ",", expr H.lt_iff_lt, ",", expr int.lt_add_one_iff, "]"] []
end

theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℚ_[p]) (n : ℤ) : ∥x∥ < (p^n) ↔ ∥x∥ ≤ (p^n - 1) :=
  by 
    rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]

end NormLeIff

end Padic

