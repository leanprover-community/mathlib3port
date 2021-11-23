import Mathbin.Data.Polynomial.Taylor 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.LinearAlgebra.AdicCompletion

/-!
# Henselian rings

In this file we set up the basic theory of Henselian (local) rings.
A ring `R` is *Henselian* at an ideal `I` if the following conditions hold:
* `I` is contained in the Jacobson radical of `R`
* for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
  there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.)

A local ring `R` is *Henselian* if it is Henselian at its maximal ideal.
In this case the first condition is automatic, and in the second condition we may ask for
`f.derivative.eval a ≠ 0`, since the quotient ring `R/I` is a field in this case.

## Main declarations

* `henselian_ring`: a typeclass on commutative rings,
  asserting that the ring is Henselian at the ideal `I`.
* `henselian_local_ring`: a typeclass on commutative rings,
   asserting that the ring is local Henselian.
* `field.henselian`: fields are Henselian local rings
* `henselian.tfae`: equivalent ways of expressing the Henselian property for local rings
* `is_adic_complete.henselian`:
  a ring `R` with ideal `I` that is `I`-adically complete is Henselian at `I`

## References

https://stacks.math.columbia.edu/tag/04GE

## Todo

After a good API for etale ring homomorphisms has been developed,
we can give more equivalent characterization os Henselian rings.

In particular, this can give a proof that factorizations into coprime polynomials can be lifted
from the residue field to the Henselian ring.

The following gist contains some code sketches in that direction.
https://gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598

-/


noncomputable theory

universe u v

open_locale BigOperators

open LocalRing Polynomial Function

-- error in RingTheory.Henselian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_local_ring_hom_of_le_jacobson_bot
{R : Type*}
[comm_ring R]
(I : ideal R)
(h : «expr ≤ »(I, ideal.jacobson «expr⊥»())) : is_local_ring_hom (ideal.quotient.mk I) :=
begin
  constructor,
  intros [ident a, ident h],
  have [] [":", expr is_unit (ideal.quotient.mk (ideal.jacobson «expr⊥»()) a)] [],
  { rw ["[", expr is_unit_iff_exists_inv, "]"] ["at", "*"],
    obtain ["⟨", ident b, ",", ident hb, "⟩", ":=", expr h],
    obtain ["⟨", ident b, ",", ident rfl, "⟩", ":=", expr ideal.quotient.mk_surjective b],
    use [expr ideal.quotient.mk _ b],
    rw ["[", "<-", expr (ideal.quotient.mk _).map_one, ",", "<-", expr (ideal.quotient.mk _).map_mul, ",", expr ideal.quotient.eq, "]"] ["at", "⊢", ident hb],
    exact [expr h hb] },
  obtain ["⟨", "⟨", ident x, ",", ident y, ",", ident h1, ",", ident h2, "⟩", ",", ident rfl, ":", expr «expr = »(x, _), "⟩", ":=", expr this],
  obtain ["⟨", ident y, ",", ident rfl, "⟩", ":=", expr ideal.quotient.mk_surjective y],
  rw ["[", "<-", expr (ideal.quotient.mk _).map_mul, ",", "<-", expr (ideal.quotient.mk _).map_one, ",", expr ideal.quotient.eq, ",", expr ideal.mem_jacobson_bot, "]"] ["at", ident h1, ident h2],
  specialize [expr h1 1],
  simp [] [] [] [] [] ["at", ident h1],
  exact [expr h1.1]
end

/-- A ring `R` is *Henselian* at an ideal `I` if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.) -/
class HenselianRing(R : Type _)[CommRingₓ R](I : Ideal R) : Prop where 
  jac : I ≤ Ideal.jacobson ⊥
  is_henselian :
  ∀ f : Polynomial R hf : f.monic a₀ : R h₁ : f.eval a₀ ∈ I h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)),
    ∃ a : R, f.is_root a ∧ a - a₀ ∈ I

/-- A local ring `R` is *Henselian* if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the residue field,
there exists a lift `a : R` of `a₀` that is a root of `f`.
(Recall that a root `b` of a polynomial `g` is *simple* if it is not a double root, so if
`g.derivative.eval b ≠ 0`.)

In other words, `R` is local Henselian if it is Henselian at the ideal `I`,
in the sense of `henselian_ring`. -/
class HenselianLocalRing(R : Type _)[CommRingₓ R] extends LocalRing R : Prop where 
  is_henselian :
  ∀ f : Polynomial R hf : f.monic a₀ : R h₁ : f.eval a₀ ∈ maximal_ideal R h₂ : IsUnit (f.derivative.eval a₀),
    ∃ a : R, f.is_root a ∧ a - a₀ ∈ maximal_ideal R

instance (priority := 100)Field.henselian (K : Type _) [Field K] : HenselianLocalRing K :=
  { is_henselian :=
      fun f hf a₀ h₁ h₂ =>
        by 
          refine' ⟨a₀, _, _⟩ <;> rwa [(maximal_ideal K).eq_bot_of_prime, Ideal.mem_bot] at *
          rw [sub_self] }

-- error in RingTheory.Henselian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem henselian_local_ring.tfae
(R : Type u)
[comm_ring R]
[local_ring R] : tfae «expr[ , ]»([henselian_local_ring R, ∀
  (f : polynomial R)
  (hf : f.monic)
  (a₀ : residue_field R)
  (h₁ : «expr = »(aeval a₀ f, 0))
  (h₂ : «expr ≠ »(aeval a₀ f.derivative, 0)), «expr∃ , »((a : R), «expr ∧ »(f.is_root a, «expr = »(residue R a, a₀))), ∀
  {K : Type u}
  [field K], by exactI [expr ∀
   (φ : «expr →+* »(R, K))
   (hφ : surjective φ)
   (f : polynomial R)
   (hf : f.monic)
   (a₀ : K)
   (h₁ : «expr = »(f.eval₂ φ a₀, 0))
   (h₂ : «expr ≠ »(f.derivative.eval₂ φ a₀, 0)), «expr∃ , »((a : R), «expr ∧ »(f.is_root a, «expr = »(φ a, a₀)))]]) :=
begin
  tfae_have [ident _3_2, ":"] [3] ["->"] [2],
  { intro [ident H],
    exact [expr H (residue R) ideal.quotient.mk_surjective] },
  tfae_have [ident _2_1, ":"] [2] ["->"] [1],
  { intros [ident H],
    constructor,
    intros [ident f, ident hf, ident a₀, ident h₁, ident h₂],
    specialize [expr H f hf (residue R a₀)],
    have [ident aux] [] [":=", expr flip mem_nonunits_iff.mp h₂],
    simp [] [] ["only"] ["[", expr aeval_def, ",", expr ring_hom.algebra_map_to_algebra, ",", expr eval₂_at_apply, ",", "<-", expr ideal.quotient.eq_zero_iff_mem, ",", "<-", expr local_ring.mem_maximal_ideal, "]"] [] ["at", ident H, ident h₁, ident aux],
    obtain ["⟨", ident a, ",", ident ha₁, ",", ident ha₂, "⟩", ":=", expr H h₁ aux],
    refine [expr ⟨a, ha₁, _⟩],
    rw ["<-", expr ideal.quotient.eq_zero_iff_mem] [],
    rwa ["[", "<-", expr sub_eq_zero, ",", "<-", expr ring_hom.map_sub, "]"] ["at", ident ha₂] },
  tfae_have [ident _1_3, ":"] [1] ["->"] [3],
  { introsI [ident hR, ident K, ident _K, ident φ, ident hφ, ident f, ident hf, ident a₀, ident h₁, ident h₂],
    obtain ["⟨", ident a₀, ",", ident rfl, "⟩", ":=", expr hφ a₀],
    have [ident H] [] [":=", expr henselian_local_ring.is_henselian f hf a₀],
    simp [] [] ["only"] ["[", "<-", expr ker_eq_maximal_ideal φ hφ, ",", expr eval₂_at_apply, ",", expr φ.mem_ker, "]"] [] ["at", ident H, ident h₁, ident h₂],
    obtain ["⟨", ident a, ",", ident ha₁, ",", ident ha₂, "⟩", ":=", expr H h₁ _],
    { refine [expr ⟨a, ha₁, _⟩],
      rwa ["[", expr φ.map_sub, ",", expr sub_eq_zero, "]"] ["at", ident ha₂] },
    { contrapose ["!"] [ident h₂],
      rwa ["[", "<-", expr mem_nonunits_iff, ",", "<-", expr local_ring.mem_maximal_ideal, ",", "<-", expr local_ring.ker_eq_maximal_ideal φ hφ, ",", expr φ.mem_ker, "]"] ["at", ident h₂] } },
  tfae_finish
end

instance  (R : Type _) [CommRingₓ R] [hR : HenselianLocalRing R] : HenselianRing R (maximal_ideal R) :=
  { jac :=
      by 
        rw [Ideal.jacobson, le_Inf_iff]
        rintro I ⟨-, hI⟩
        exact (eq_maximal_ideal hI).Ge,
    is_henselian :=
      by 
        intro f hf a₀ h₁ h₂ 
        refine' HenselianLocalRing.is_henselian f hf a₀ h₁ _ 
        contrapose! h₂ 
        rw [←mem_nonunits_iff, ←LocalRing.mem_maximal_ideal, ←Ideal.Quotient.eq_zero_iff_mem] at h₂ 
        rw [h₂]
        exact not_is_unit_zero }

-- error in RingTheory.Henselian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A ring `R` that is `I`-adically complete is Henselian at `I`. -/
@[priority 100]
instance is_adic_complete.henselian_ring
(R : Type*)
[comm_ring R]
(I : ideal R)
[is_adic_complete I R] : henselian_ring R I :=
{ jac := is_adic_complete.le_jacobson_bot _,
  is_henselian := begin
    intros [ident f, ident hf, ident a₀, ident h₁, ident h₂],
    classical,
    let [ident f'] [] [":=", expr f.derivative],
    let [ident c] [":", expr exprℕ() → R] [":=", expr λ
     n, nat.rec_on n a₀ (λ _ b, «expr - »(b, «expr * »(f.eval b, ring.inverse (f'.eval b))))],
    have [ident hc] [":", expr ∀
     n, «expr = »(c «expr + »(n, 1), «expr - »(c n, «expr * »(f.eval (c n), ring.inverse (f'.eval (c n)))))] [],
    { intro [ident n],
      dsimp ["only"] ["[", expr c, ",", expr nat.rec_add_one, "]"] [] [],
      refl },
    have [ident hc_mod] [":", expr ∀ n, «expr ≡ [SMOD ]»(c n, a₀, I)] [],
    { intro [ident n],
      induction [expr n] [] ["with", ident n, ident ih] [],
      { refl },
      rw ["[", expr nat.succ_eq_add_one, ",", expr hc, ",", expr sub_eq_add_neg, ",", "<-", expr add_zero a₀, "]"] [],
      refine [expr ih.add _],
      rw ["[", expr smodeq.zero, ",", expr ideal.neg_mem_iff, "]"] [],
      refine [expr I.mul_mem_right _ _],
      rw ["[", "<-", expr smodeq.zero, "]"] ["at", ident h₁, "⊢"],
      exact [expr (ih.eval f).trans h₁] },
    have [ident hf'c] [":", expr ∀ n, is_unit (f'.eval (c n))] [],
    { intro [ident n],
      haveI [] [] [":=", expr is_local_ring_hom_of_le_jacobson_bot I (is_adic_complete.le_jacobson_bot I)],
      apply [expr is_unit_of_map_unit (ideal.quotient.mk I)],
      convert [] [expr h₂] ["using", 1],
      exact [expr smodeq.def.mp ((hc_mod n).eval _)] },
    have [ident hfcI] [":", expr ∀ n, «expr ∈ »(f.eval (c n), «expr ^ »(I, «expr + »(n, 1)))] [],
    { intro [ident n],
      induction [expr n] [] ["with", ident n, ident ih] [],
      { simpa [] [] ["only"] ["[", expr pow_one, "]"] [] [] },
      simp [] [] ["only"] ["[", expr nat.succ_eq_add_one, "]"] [] [],
      rw ["[", "<-", expr taylor_eval_sub (c n), ",", expr hc, "]"] [],
      simp [] [] ["only"] ["[", expr sub_eq_add_neg, ",", expr add_neg_cancel_comm, "]"] [] [],
      rw ["[", expr eval_eq_sum, ",", expr sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ",", "<-", expr finset.sum_range_add_sum_Ico _ (nat.le_add_left _ _), "]"] [],
      swap,
      { intro [ident i],
        rw [expr zero_mul] [] },
      refine [expr ideal.add_mem _ _ _],
      { simp [] [] ["only"] ["[", expr finset.sum_range_succ, ",", expr taylor_coeff_one, ",", expr mul_one, ",", expr pow_one, ",", expr taylor_coeff_zero, ",", expr mul_neg_eq_neg_mul_symm, ",", expr finset.sum_singleton, ",", expr finset.range_one, ",", expr pow_zero, "]"] [] [],
        rw ["[", expr mul_left_comm, ",", expr ring.mul_inverse_cancel _ (hf'c n), ",", expr mul_one, ",", expr add_neg_self, "]"] [],
        exact [expr ideal.zero_mem _] },
      { refine [expr submodule.sum_mem _ _],
        simp [] [] ["only"] ["[", expr finset.mem_Ico, "]"] [] [],
        rintro [ident i, "⟨", ident h2i, ",", ident hi, "⟩"],
        have [ident aux] [":", expr «expr ≤ »(«expr + »(n, 2), «expr * »(i, «expr + »(n, 1)))] [],
        { transitivity [expr «expr * »(2, «expr + »(n, 1))]; nlinarith [] ["only"] ["[", expr h2i, "]"] },
        refine [expr ideal.mul_mem_left _ _ (ideal.pow_le_pow aux _)],
        rw ["[", expr pow_mul', "]"] [],
        refine [expr ideal.pow_mem_pow «expr $ »((ideal.neg_mem_iff _).2, ideal.mul_mem_right _ _ ih) _] } },
    have [ident aux] [":", expr ∀
     m n, «expr ≤ »(m, n) → «expr ≡ [SMOD ]»(c m, c n, («expr • »(«expr ^ »(I, m), «expr⊤»()) : ideal R))] [],
    { intros [ident m, ident n, ident hmn],
      rw ["[", "<-", expr ideal.one_eq_top, ",", expr algebra.id.smul_eq_mul, ",", expr mul_one, "]"] [],
      obtain ["⟨", ident k, ",", ident rfl, "⟩", ":=", expr nat.exists_eq_add_of_le hmn],
      clear [ident hmn],
      induction [expr k] [] ["with", ident k, ident ih] [],
      { rw [expr add_zero] [] },
      rw ["[", expr nat.succ_eq_add_one, ",", "<-", expr add_assoc, ",", expr hc, ",", "<-", expr add_zero (c m), ",", expr sub_eq_add_neg, "]"] [],
      refine [expr ih.add _],
      symmetry,
      rw ["[", expr smodeq.zero, ",", expr ideal.neg_mem_iff, "]"] [],
      refine [expr ideal.mul_mem_right _ _ (ideal.pow_le_pow _ (hfcI _))],
      rw ["[", expr add_assoc, "]"] [],
      exact [expr le_self_add] },
    obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr is_precomplete.prec' c aux],
    refine [expr ⟨a, _, _⟩],
    { show [expr f.is_root a],
      suffices [] [":", expr ∀ n, «expr ≡ [SMOD ]»(f.eval a, 0, («expr • »(«expr ^ »(I, n), «expr⊤»()) : ideal R))],
      { from [expr is_Hausdorff.haus' _ this] },
      intro [ident n],
      specialize [expr ha n],
      rw ["[", "<-", expr ideal.one_eq_top, ",", expr algebra.id.smul_eq_mul, ",", expr mul_one, "]"] ["at", ident ha, "⊢"],
      refine [expr (ha.symm.eval f).trans _],
      rw ["[", expr smodeq.zero, "]"] [],
      exact [expr ideal.pow_le_pow le_self_add (hfcI _)] },
    { show [expr «expr ∈ »(«expr - »(a, a₀), I)],
      specialize [expr ha 1],
      rw ["[", expr hc, ",", expr pow_one, ",", "<-", expr ideal.one_eq_top, ",", expr algebra.id.smul_eq_mul, ",", expr mul_one, ",", expr sub_eq_add_neg, "]"] ["at", ident ha],
      rw ["[", "<-", expr smodeq.sub_mem, ",", "<-", expr add_zero a₀, "]"] [],
      refine [expr ha.symm.trans (smodeq.refl.add _)],
      rw ["[", expr smodeq.zero, ",", expr ideal.neg_mem_iff, "]"] [],
      exact [expr ideal.mul_mem_right _ _ h₁] }
  end }

