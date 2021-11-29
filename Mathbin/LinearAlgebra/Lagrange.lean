import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : s → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.

-/


noncomputable theory

open_locale BigOperators Classical

universe u

namespace Lagrange

variable {F : Type u} [DecidableEq F] [Field F] (s : Finset F)

variable {F' : Type u} [Field F'] (s' : Finset F')

open Polynomial

/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
def basis (x : F) : Polynomial F :=
  ∏y in s.erase x, C ((x - y)⁻¹)*X - C y

@[simp]
theorem basis_empty (x : F) : basis ∅ x = 1 :=
  rfl

@[simp]
theorem eval_basis_self (x : F) : (basis s x).eval x = 1 :=
  by 
    rw [basis, ←coe_eval_ring_hom, (eval_ring_hom x).map_prod, coe_eval_ring_hom, Finset.prod_eq_one]
    intro y hy 
    simpRw [eval_mul, eval_sub, eval_C, eval_X]
    exact inv_mul_cancel (sub_ne_zero_of_ne (Finset.ne_of_mem_erase hy).symm)

@[simp]
theorem eval_basis_ne (x y : F) (h1 : y ∈ s) (h2 : y ≠ x) : (basis s x).eval y = 0 :=
  by 
    rw [basis, ←coe_eval_ring_hom, (eval_ring_hom y).map_prod, coe_eval_ring_hom,
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h2, h1⟩)]
    simpRw [eval_mul, eval_sub, eval_C, eval_X, sub_self, mul_zero]

theorem eval_basis (x y : F) (h : y ∈ s) : (basis s x).eval y = if y = x then 1 else 0 :=
  by 
    splitIfs with H
    ·
      subst H 
      apply eval_basis_self
    ·
      exact eval_basis_ne s x y h H

-- error in LinearAlgebra.Lagrange: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem nat_degree_basis (x : F) (hx : «expr ∈ »(x, s)) : «expr = »((basis s x).nat_degree, «expr - »(s.card, 1)) :=
begin
  unfold [ident basis] [],
  generalize [ident hsx] [":"] [expr «expr = »(s.erase x, sx)],
  have [] [":", expr «expr ∉ »(x, sx)] [":=", expr «expr ▸ »(hsx, finset.not_mem_erase x s)],
  rw ["[", "<-", expr finset.insert_erase hx, ",", expr hsx, ",", expr finset.card_insert_of_not_mem this, ",", expr add_tsub_cancel_right, "]"] [],
  clear [ident hx, ident hsx, ident s],
  revert [ident this],
  apply [expr sx.induction_on],
  { intros [ident hx],
    rw ["[", expr finset.prod_empty, ",", expr nat_degree_one, "]"] [],
    refl },
  { intros [ident y, ident s, ident hys, ident ih, ident hx],
    rw ["[", expr finset.mem_insert, ",", expr not_or_distrib, "]"] ["at", ident hx],
    have [ident h1] [":", expr «expr ≠ »(C «expr ⁻¹»(«expr - »(x, y)), C 0)] [":=", expr λ
     h, hx.1 «expr $ »(eq_of_sub_eq_zero, «expr $ »(inv_eq_zero.1, C_inj.1 h))],
    have [ident h2] [":", expr «expr ≠ »(«expr - »(«expr ^ »(X, 1), C y), 0)] [":=", expr by convert [] [expr X_pow_sub_C_ne_zero zero_lt_one y] []],
    rw [expr C_0] ["at", ident h1],
    rw [expr pow_one] ["at", ident h2],
    rw ["[", expr finset.prod_insert hys, ",", expr nat_degree_mul (mul_ne_zero h1 h2), ",", expr ih hx.2, ",", expr finset.card_insert_of_not_mem hys, ",", expr nat_degree_mul h1 h2, ",", expr nat_degree_C, ",", expr zero_add, ",", expr nat_degree, ",", expr degree_X_sub_C, ",", expr add_comm, "]"] [],
    refl,
    rw ["[", expr ne, ",", expr finset.prod_eq_zero_iff, "]"] [],
    rintro ["⟨", ident z, ",", ident hzs, ",", ident hz, "⟩"],
    rw [expr mul_eq_zero] ["at", ident hz],
    cases [expr hz] ["with", ident hz, ident hz],
    { rw ["[", "<-", expr C_0, ",", expr C_inj, ",", expr inv_eq_zero, ",", expr sub_eq_zero, "]"] ["at", ident hz],
      exact [expr hx.2 «expr ▸ »(hz.symm, hzs)] },
    { rw ["<-", expr pow_one (X : polynomial F)] ["at", ident hz],
      exact [expr X_pow_sub_C_ne_zero zero_lt_one _ hz] } }
end

variable (f : s → F)

/-- Lagrange interpolation: given a finset `s` and a function `f : s → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate : Polynomial F :=
  ∑x in s.attach, C (f x)*basis s x

@[simp]
theorem interpolate_empty f : interpolate (∅ : Finset F) f = 0 :=
  rfl

@[simp]
theorem eval_interpolate x (H : x ∈ s) : eval x (interpolate s f) = f ⟨x, H⟩ :=
  by 
    rw [interpolate, ←coe_eval_ring_hom, (eval_ring_hom x).map_sum, coe_eval_ring_hom,
      Finset.sum_eq_single (⟨x, H⟩ : { x // x ∈ s })]
    ·
      rw [eval_mul, eval_C, Subtype.coe_mk, eval_basis_self, mul_oneₓ]
    ·
      rintro ⟨y, hy⟩ _ hyx 
      rw [eval_mul, Subtype.coe_mk, eval_basis_ne s y x H, mul_zero]
      ·
        rintro rfl 
        exact hyx rfl
    ·
      intro h 
      exact absurd (Finset.mem_attach _ _) h

theorem degree_interpolate_lt : (interpolate s f).degree < s.card :=
  if H : s = ∅ then
    by 
      subst H 
      rw [interpolate_empty, degree_zero]
      exact WithBot.bot_lt_coe _
  else
    (degree_sum_le _ _).trans_lt$
      (Finset.sup_lt_iff$ WithBot.bot_lt_coe s.card).2$
        fun b _ =>
          calc (C (f b)*basis s b).degree ≤ (C (f b)).degree+(basis s b).degree := degree_mul_le _ _ 
            _ ≤ 0+(basis s b).degree := add_le_add_right degree_C_le _ 
            _ = (basis s b).degree := zero_addₓ _ 
            _ ≤ (basis s b).natDegree := degree_le_nat_degree 
            _ = (s.card - 1 : ℕ) :=
            by 
              rw [nat_degree_basis s b b.2]
            _ < s.card := WithBot.coe_lt_coe.2 (Nat.pred_ltₓ$ mt Finset.card_eq_zero.1 H)
            

/-- Linear version of `interpolate`. -/
def linterpolate : (s → F) →ₗ[F] Polynomial F :=
  { toFun := interpolate s,
    map_add' :=
      fun f g =>
        by 
          simpRw [interpolate, ←Finset.sum_add_distrib, ←add_mulₓ, ←C_add]
          rfl,
    map_smul' :=
      fun c f =>
        by 
          simpRw [interpolate, Finset.smul_sum, C_mul', smul_smul]
          rfl }

@[simp]
theorem interpolate_add f g : interpolate s (f+g) = interpolate s f+interpolate s g :=
  (linterpolate s).map_add f g

@[simp]
theorem interpolate_zero : interpolate s 0 = 0 :=
  (linterpolate s).map_zero

@[simp]
theorem interpolate_neg f : interpolate s (-f) = -interpolate s f :=
  (linterpolate s).map_neg f

@[simp]
theorem interpolate_sub f g : interpolate s (f - g) = interpolate s f - interpolate s g :=
  (linterpolate s).map_sub f g

@[simp]
theorem interpolate_smul (c : F) f : interpolate s (c • f) = c • interpolate s f :=
  (linterpolate s).map_smul c f

theorem eq_zero_of_eval_eq_zero {f : Polynomial F'} (hf1 : f.degree < s'.card) (hf2 : ∀ x _ : x ∈ s', f.eval x = 0) :
  f = 0 :=
  by_contradiction$
    fun hf3 =>
      not_le_of_lt hf1$
        calc (s'.card : WithBot ℕ) ≤ f.roots.to_finset.card :=
          WithBot.coe_le_coe.2$
            Finset.card_le_of_subset$ fun x hx => Multiset.mem_to_finset.mpr$ (mem_roots hf3).2$ hf2 x hx 
          _ ≤ f.roots.card := WithBot.coe_le_coe.2$ f.roots.to_finset_card_le 
          _ ≤ f.degree := card_roots hf3
          

theorem eq_of_eval_eq {f g : Polynomial F'} (hf : f.degree < s'.card) (hg : g.degree < s'.card)
  (hfg : ∀ x _ : x ∈ s', f.eval x = g.eval x) : f = g :=
  eq_of_sub_eq_zero$
    eq_zero_of_eval_eq_zero s' (lt_of_le_of_ltₓ (degree_sub_le f g)$ max_ltₓ hf hg)
      fun x hx =>
        by 
          rw [eval_sub, hfg x hx, sub_self]

theorem eq_interpolate (f : Polynomial F) (hf : f.degree < s.card) : (interpolate s fun x => f.eval x) = f :=
  eq_of_eval_eq s (degree_interpolate_lt s _) hf$ fun x hx => eval_interpolate s _ x hx

/-- Lagrange interpolation induces isomorphism between functions from `s` and polynomials
of degree less than `s.card`. -/
def fun_equiv_degree_lt : degree_lt F s.card ≃ₗ[F] s → F :=
  { toFun := fun f x => f.1.eval x, map_add' := fun f g => funext$ fun x => eval_add,
    map_smul' :=
      fun c f =>
        funext$
          fun x =>
            by 
              change eval («expr↑ » x) (c • f).val = (c • fun x : s => eval («expr↑ » x) f.val) x 
              rw [Pi.smul_apply, smul_eq_mul, ←@eval_C F c _ x, ←eval_mul, eval_C, C_mul']
              rfl,
    invFun := fun f => ⟨interpolate s f, mem_degree_lt.2$ degree_interpolate_lt s f⟩,
    left_inv := fun f => Subtype.eq$ eq_interpolate s f$ mem_degree_lt.1 f.2,
    right_inv := fun f => funext$ fun ⟨x, hx⟩ => eval_interpolate s f x hx }

end Lagrange

