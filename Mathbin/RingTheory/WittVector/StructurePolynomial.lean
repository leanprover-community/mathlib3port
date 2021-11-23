import Mathbin.Data.Fin.VecNotation 
import Mathbin.FieldTheory.Finite.Polynomial 
import Mathbin.NumberTheory.Basic 
import Mathbin.RingTheory.WittVector.WittPolynomial

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : mv_polynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → mv_polynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`witt_structure_int_exists_unique`)
```
bind₁ φ (witt_polynomial p ℤ n) = bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `witt_structure_int`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → mv_polynomial (bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `witt_structure_int_exists_unique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `mv_polynomial ℕ ℚ`.
We therefore obtain a family of polynomials `witt_structure_rat Φ`
for every `Φ : mv_polynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `witt_structure_rat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_witt_structure_int`, which proves that upon mapping the coefficients
of `witt_structure_int Φ n` from the integers to the rationals,
one obtains `witt_structure_rat Φ n`.
Ultimately, the proof of `map_witt_structure_int` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [comm_ring R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `witt_structure_rat Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
  associated with `Φ : mv_polynomial idx ℚ` and satisfying the property explained above.
* `witt_structure_rat_prop`: the proof that `witt_structure_rat` indeed satisfies the property.
* `witt_structure_int Φ`: the family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℤ`
  associated with `Φ : mv_polynomial idx ℤ` and satisfying the property explained above.
* `map_witt_structure_int`: the proof that the integral polynomials `with_structure_int Φ`
  are equal to `witt_structure_rat Φ` when mapped to polynomials with rational coefficients.
* `witt_structure_int_prop`: the proof that `witt_structure_int` indeed satisfies the property.
* Five families of polynomials that will be used to define the ring structure
  on the ring of Witt vectors:
  - `witt_vector.witt_zero`
  - `witt_vector.witt_one`
  - `witt_vector.witt_add`
  - `witt_vector.witt_mul`
  - `witt_vector.witt_neg`
  (We also define `witt_vector.witt_sub`, and later we will prove that it describes subtraction,
  which is defined as `λ a b, a + -b`. See `witt_vector.sub_coeff` for this proof.)

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


open MvPolynomial

open Set

open finset(range)

open finsupp(single)

attribute [-simp] coe_eval₂_hom

variable{p : ℕ}{R : Type _}{idx : Type _}[CommRingₓ R]

open_locale Witt

open_locale BigOperators

section PPrime

variable(p)[hp : Fact p.prime]

include hp

/-- `witt_structure_rat Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (witt_structure_rat p Φ) (witt_polynomial p ℚ n) =
bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_rat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_rat_prop` for this property,
and `witt_structure_rat_exists_unique` for the fact that `witt_structure_rat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `witt_structure_int` for the version with integral coefficients,
and `map_witt_structure_int` for the fact that it is equal to `witt_structure_rat`
when mapped to polynomials over the rationals. -/
noncomputable def wittStructureRat (Φ : MvPolynomial idx ℚ) (n : ℕ) : MvPolynomial (idx × ℕ) ℚ :=
  bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) (xInTermsOfW p ℚ n)

theorem witt_structure_rat_prop (Φ : MvPolynomial idx ℚ) (n : ℕ) :
  bind₁ (wittStructureRat p Φ) (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  calc
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) =
      bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ ℚ k)) Φ) (bind₁ (xInTermsOfW p ℚ) (W_ ℚ n)) :=
    by 
      rw [bind₁_bind₁]
      apply eval₂_hom_congr (RingHom.ext_rat _ _) rfl rfl 
    _ = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
    by 
      rw [bind₁_X_in_terms_of_W_witt_polynomial p _ n, bind₁_X_right]
    

theorem witt_structure_rat_exists_unique (Φ : MvPolynomial idx ℚ) :
  ∃!φ : ℕ → MvPolynomial (idx × ℕ) ℚ, ∀ n : ℕ, bind₁ φ (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  by 
    refine' ⟨wittStructureRat p Φ, _, _⟩
    ·
      intro n 
      apply witt_structure_rat_prop
    ·
      intro φ H 
      funext n 
      rw
        [show φ n = bind₁ φ (bind₁ (W_ ℚ) (xInTermsOfW p ℚ n))by 
          rw [bind₁_witt_polynomial_X_in_terms_of_W p, bind₁_X_right]]
      rw [bind₁_bind₁]
      exact eval₂_hom_congr (RingHom.ext_rat _ _) (funext H) rfl

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem witt_structure_rat_rec_aux
(Φ : mv_polynomial idx exprℚ())
(n : exprℕ()) : «expr = »(«expr * »(witt_structure_rat p Φ n, C («expr ^ »(p, n) : exprℚ())), «expr - »(bind₁ (λ
   b, rename (λ
    i, (b, i)) (exprW_() exprℚ() n)) Φ, «expr∑ in , »((i), range n, «expr * »(C («expr ^ »(p, i) : exprℚ()), «expr ^ »(witt_structure_rat p Φ i, «expr ^ »(p, «expr - »(n, i))))))) :=
begin
  have [] [] [":=", expr X_in_terms_of_W_aux p exprℚ() n],
  replace [] [] [":=", expr congr_arg (bind₁ (λ
     k : exprℕ(), bind₁ (λ i, rename (prod.mk i) (exprW_() exprℚ() k)) Φ)) this],
  rw ["[", expr alg_hom.map_mul, ",", expr bind₁_C_right, "]"] ["at", ident this],
  rw ["[", expr witt_structure_rat, ",", expr this, "]"] [],
  clear [ident this],
  conv_lhs [] [] { simp ["only"] ["[", expr alg_hom.map_sub, ",", expr bind₁_X_right, "]"] [] },
  rw [expr sub_right_inj] [],
  simp [] [] ["only"] ["[", expr alg_hom.map_sum, ",", expr alg_hom.map_mul, ",", expr bind₁_C_right, ",", expr alg_hom.map_pow, "]"] [] [],
  refl
end

/-- Write `witt_structure_rat p φ n` in terms of `witt_structure_rat p φ i` for `i < n`. -/
theorem witt_structure_rat_rec (Φ : MvPolynomial idx ℚ) (n : ℕ) :
  wittStructureRat p Φ n =
    C
        (1 / (p^n) :
        ℚ)*bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
        ∑i in range n, C (p^i : ℚ)*wittStructureRat p Φ i^p^n - i :=
  by 
    calc wittStructureRat p Φ n = C (1 / (p^n) : ℚ)*wittStructureRat p Φ n*C (p^n : ℚ) := _ _ = _ :=
      by 
        rw [witt_structure_rat_rec_aux]
    rw [mul_left_commₓ, ←C_mul, div_mul_cancel, C_1, mul_oneₓ]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)

/-- `witt_structure_int Φ` is a family of polynomials `ℕ → mv_polynomial (idx × ℕ) ℤ`
that are uniquely characterised by the property that
```
bind₁ (witt_structure_int p Φ) (witt_polynomial p ℤ n) =
bind₁ (λ i, (rename (prod.mk i) (witt_polynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `witt_structure_int Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `witt_structure_int_prop` for this property,
and `witt_structure_int_exists_unique` for the fact that `witt_structure_int`
gives the unique family of polynomials with this property. -/
noncomputable def wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) : MvPolynomial (idx × ℕ) ℤ :=
  Finsupp.mapRange Rat.num (Rat.coe_int_num 0) (wittStructureRat p (map (Int.castRingHom ℚ) Φ) n)

variable{p}

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bind₁_rename_expand_witt_polynomial
(Φ : mv_polynomial idx exprℤ())
(n : exprℕ())
(IH : ∀
 m : exprℕ(), «expr < »(m, «expr + »(n, 1)) → «expr = »(map (int.cast_ring_hom exprℚ()) (witt_structure_int p Φ m), witt_structure_rat p (map (int.cast_ring_hom exprℚ()) Φ) m)) : «expr = »(bind₁ (λ
  b, rename (λ
   i, (b, i)) (expand p (exprW_() exprℤ() n))) Φ, bind₁ (λ
  i, expand p (witt_structure_int p Φ i)) (exprW_() exprℤ() n)) :=
begin
  apply [expr mv_polynomial.map_injective (int.cast_ring_hom exprℚ()) int.cast_injective],
  simp [] [] ["only"] ["[", expr map_bind₁, ",", expr map_rename, ",", expr map_expand, ",", expr rename_expand, ",", expr map_witt_polynomial, "]"] [] [],
  have [ident key] [] [":=", expr (witt_structure_rat_prop p (map (int.cast_ring_hom exprℚ()) Φ) n).symm],
  apply_fun [expr expand p] ["at", ident key] [],
  simp [] [] ["only"] ["[", expr expand_bind₁, "]"] [] ["at", ident key],
  rw [expr key] [],
  clear [ident key],
  apply [expr eval₂_hom_congr' rfl _ rfl],
  rintro [ident i, ident hi, "-"],
  rw ["[", expr witt_polynomial_vars, ",", expr finset.mem_range, "]"] ["at", ident hi],
  simp [] [] ["only"] ["[", expr IH i hi, "]"] [] []
end

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum
(Φ : mv_polynomial idx exprℤ())
(n : exprℕ())
(IH : ∀
 m : exprℕ(), «expr < »(m, n) → «expr = »(map (int.cast_ring_hom exprℚ()) (witt_structure_int p Φ m), witt_structure_rat p (map (int.cast_ring_hom exprℚ()) Φ) m)) : «expr ∣ »(C «expr↑ »(«expr ^ »(p, n)), «expr - »(bind₁ (λ
   b : idx, rename (λ
    i, (b, i)) (witt_polynomial p exprℤ() n)) Φ, «expr∑ in , »((i), range n, «expr * »(C «expr ^ »(«expr↑ »(p), i), «expr ^ »(witt_structure_int p Φ i, «expr ^ »(p, «expr - »(n, i))))))) :=
begin
  cases [expr n] [],
  { simp [] [] ["only"] ["[", expr is_unit_one, ",", expr int.coe_nat_zero, ",", expr int.coe_nat_succ, ",", expr zero_add, ",", expr pow_zero, ",", expr C_1, ",", expr is_unit.dvd, "]"] [] [] },
  have [ident key] [] [":=", expr bind₁_rename_expand_witt_polynomial Φ n IH],
  apply_fun [expr map (int.cast_ring_hom (zmod «expr ^ »(p, «expr + »(n, 1))))] ["at", ident key] [],
  conv_lhs ["at", ident key] [] { simp ["only"] ["[", expr map_bind₁, ",", expr map_rename, ",", expr map_expand, ",", expr map_witt_polynomial, "]"] [] },
  rw ["[", expr nat.succ_eq_add_one, ",", expr C_dvd_iff_zmod, ",", expr ring_hom.map_sub, ",", expr sub_eq_zero, ",", expr map_bind₁, "]"] [],
  simp [] [] ["only"] ["[", expr map_rename, ",", expr map_witt_polynomial, ",", expr witt_polynomial_zmod_self, "]"] [] [],
  rw [expr key] [],
  clear [ident key, ident IH],
  rw ["[", expr bind₁, ",", expr aeval_witt_polynomial, ",", expr ring_hom.map_sum, ",", expr ring_hom.map_sum, ",", expr finset.sum_congr rfl, "]"] [],
  intros [ident k, ident hk],
  rw ["[", expr finset.mem_range, ",", expr nat.lt_succ_iff, "]"] ["at", ident hk],
  simp [] [] ["only"] ["[", "<-", expr sub_eq_zero, ",", "<-", expr ring_hom.map_sub, ",", "<-", expr C_dvd_iff_zmod, ",", expr C_eq_coe_nat, ",", "<-", expr mul_sub, ",", "<-", expr int.nat_cast_eq_coe_nat, ",", "<-", expr nat.cast_pow, "]"] [] [],
  rw [expr show «expr = »(«expr ^ »(p, «expr + »(n, 1)), «expr * »(«expr ^ »(p, k), «expr ^ »(p, «expr + »(«expr - »(n, k), 1)))), { rw ["[", "<-", expr pow_add, ",", "<-", expr add_assoc, "]"] [],
     congr' [2] [],
     rw ["[", expr add_comm, ",", "<-", expr tsub_eq_iff_eq_add_of_le hk, "]"] [] }] [],
  rw ["[", expr nat.cast_mul, ",", expr nat.cast_pow, ",", expr nat.cast_pow, "]"] [],
  apply [expr mul_dvd_mul_left],
  rw [expr show «expr = »(«expr ^ »(p, «expr - »(«expr + »(n, 1), k)), «expr * »(p, «expr ^ »(p, «expr - »(n, k)))), { rw ["[", "<-", expr pow_succ, ",", "<-", expr tsub_add_eq_add_tsub hk, "]"] [] }] [],
  rw ["[", expr pow_mul, "]"] [],
  apply [expr dvd_sub_pow_of_dvd_sub],
  rw ["[", "<-", expr C_eq_coe_nat, ",", expr int.nat_cast_eq_coe_nat, ",", expr C_dvd_iff_zmod, ",", expr ring_hom.map_sub, ",", expr sub_eq_zero, ",", expr map_expand, ",", expr ring_hom.map_pow, ",", expr mv_polynomial.expand_zmod, "]"] []
end

variable(p)

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem map_witt_structure_int
(Φ : mv_polynomial idx exprℤ())
(n : exprℕ()) : «expr = »(map (int.cast_ring_hom exprℚ()) (witt_structure_int p Φ n), witt_structure_rat p (map (int.cast_ring_hom exprℚ()) Φ) n) :=
begin
  apply [expr nat.strong_induction_on n],
  clear [ident n],
  intros [ident n, ident IH],
  rw ["[", expr witt_structure_int, ",", expr map_map_range_eq_iff, ",", expr int.coe_cast_ring_hom, "]"] [],
  intro [ident c],
  rw ["[", expr witt_structure_rat_rec, ",", expr coeff_C_mul, ",", expr mul_comm, ",", expr mul_div_assoc', ",", expr mul_one, "]"] [],
  have [ident sum_induction_steps] [":", expr «expr = »(map (int.cast_ring_hom exprℚ()) «expr∑ in , »((i), range n, «expr * »(C («expr ^ »(p, i) : exprℤ()), «expr ^ »(witt_structure_int p Φ i, «expr ^ »(p, «expr - »(n, i))))), «expr∑ in , »((i), range n, «expr * »(C («expr ^ »(p, i) : exprℚ()), «expr ^ »(witt_structure_rat p (map (int.cast_ring_hom exprℚ()) Φ) i, «expr ^ »(p, «expr - »(n, i))))))] [],
  { rw ["[", expr ring_hom.map_sum, "]"] [],
    apply [expr finset.sum_congr rfl],
    intros [ident i, ident hi],
    rw [expr finset.mem_range] ["at", ident hi],
    simp [] [] ["only"] ["[", expr IH i hi, ",", expr ring_hom.map_mul, ",", expr ring_hom.map_pow, ",", expr map_C, "]"] [] [],
    refl },
  simp [] [] ["only"] ["[", "<-", expr sum_induction_steps, ",", "<-", expr map_witt_polynomial p (int.cast_ring_hom exprℚ()), ",", "<-", expr map_rename, ",", "<-", expr map_bind₁, ",", "<-", expr ring_hom.map_sub, ",", expr coeff_map, "]"] [] [],
  rw [expr show «expr = »(«expr ^ »((p : exprℚ()), n), ((«expr ^ »(p, n) : exprℕ()) : exprℤ())), by norm_cast []] [],
  rw ["[", "<-", expr rat.denom_eq_one_iff, ",", expr ring_hom.eq_int_cast, ",", expr rat.denom_div_cast_eq_one_iff, "]"] [],
  swap,
  { exact_mod_cast [expr pow_ne_zero n hp.1.ne_zero] },
  revert [ident c],
  rw ["[", "<-", expr C_dvd_iff_dvd_coeff, "]"] [],
  exact [expr C_p_pow_dvd_bind₁_rename_witt_polynomial_sub_sum Φ n IH]
end

variable(p)

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem witt_structure_int_prop
(Φ : mv_polynomial idx exprℤ())
(n) : «expr = »(bind₁ (witt_structure_int p Φ) (witt_polynomial p exprℤ() n), bind₁ (λ
  i, rename (prod.mk i) (exprW_() exprℤ() n)) Φ) :=
begin
  apply [expr mv_polynomial.map_injective (int.cast_ring_hom exprℚ()) int.cast_injective],
  have [] [] [":=", expr witt_structure_rat_prop p (map (int.cast_ring_hom exprℚ()) Φ) n],
  simpa [] [] ["only"] ["[", expr map_bind₁, ",", "<-", expr eval₂_hom_map_hom, ",", expr eval₂_hom_C_left, ",", expr map_rename, ",", expr map_witt_polynomial, ",", expr alg_hom.coe_to_ring_hom, ",", expr map_witt_structure_int, "]"] [] []
end

theorem eq_witt_structure_int (Φ : MvPolynomial idx ℤ) (φ : ℕ → MvPolynomial (idx × ℕ) ℤ)
  (h : ∀ n, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ) :
  φ = wittStructureInt p Φ :=
  by 
    funext k 
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective 
    rw [map_witt_structure_int]
    refine' congr_funₓ _ k 
    apply unique_of_exists_unique (witt_structure_rat_exists_unique p (map (Int.castRingHom ℚ) Φ))
    ·
      intro n 
      specialize h n 
      applyFun map (Int.castRingHom ℚ)  at h 
      simpa only [map_bind₁, ←eval₂_hom_map_hom, eval₂_hom_C_left, map_rename, map_witt_polynomial,
        AlgHom.coe_to_ring_hom] using h
    ·
      intro n 
      apply witt_structure_rat_prop

theorem witt_structure_int_exists_unique (Φ : MvPolynomial idx ℤ) :
  ∃!φ : ℕ → MvPolynomial (idx × ℕ) ℤ,
    ∀ n : ℕ, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ ℤ n)) Φ :=
  ⟨wittStructureInt p Φ, witt_structure_int_prop _ _, eq_witt_structure_int _ _⟩

theorem witt_structure_prop (Φ : MvPolynomial idx ℤ) n :
  aeval (fun i => map (Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p ℤ n) =
    aeval (fun i => rename (Prod.mk i) (W n)) Φ :=
  by 
    convert congr_argₓ (map (Int.castRingHom R)) (witt_structure_int_prop p Φ n) using 1 <;>
      rw [hom_bind₁] <;> apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    ·
      rfl
    ·
      simp only [map_rename, map_witt_polynomial]

theorem witt_structure_int_rename {σ : Type _} (Φ : MvPolynomial idx ℤ) (f : idx → σ) (n : ℕ) :
  wittStructureInt p (rename f Φ) n = rename (Prod.mapₓ f id) (wittStructureInt p Φ n) :=
  by 
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective 
    simp only [map_rename, map_witt_structure_int, wittStructureRat, rename_bind₁, rename_rename, bind₁_rename]
    rfl

@[simp]
theorem constant_coeff_witt_structure_rat_zero (Φ : MvPolynomial idx ℚ) :
  constant_coeff (wittStructureRat p Φ 0) = constant_coeff Φ :=
  by 
    simp only [wittStructureRat, bind₁, map_aeval, X_in_terms_of_W_zero, constant_coeff_rename,
      constant_coeff_witt_polynomial, aeval_X, constant_coeff_comp_algebra_map, eval₂_hom_zero', RingHom.id_apply]

theorem constant_coeff_witt_structure_rat (Φ : MvPolynomial idx ℚ) (h : constant_coeff Φ = 0) (n : ℕ) :
  constant_coeff (wittStructureRat p Φ n) = 0 :=
  by 
    simp only [wittStructureRat, eval₂_hom_zero', h, bind₁, map_aeval, constant_coeff_rename,
      constant_coeff_witt_polynomial, constant_coeff_comp_algebra_map, RingHom.id_apply, constant_coeff_X_in_terms_of_W]

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem constant_coeff_witt_structure_int_zero
(Φ : mv_polynomial idx exprℤ()) : «expr = »(constant_coeff (witt_structure_int p Φ 0), constant_coeff Φ) :=
begin
  have [ident inj] [":", expr function.injective (int.cast_ring_hom exprℚ())] [],
  { intros [ident m, ident n],
    exact [expr int.cast_inj.mp] },
  apply [expr inj],
  rw ["[", "<-", expr constant_coeff_map, ",", expr map_witt_structure_int, ",", expr constant_coeff_witt_structure_rat_zero, ",", expr constant_coeff_map, "]"] []
end

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem constant_coeff_witt_structure_int
(Φ : mv_polynomial idx exprℤ())
(h : «expr = »(constant_coeff Φ, 0))
(n : exprℕ()) : «expr = »(constant_coeff (witt_structure_int p Φ n), 0) :=
begin
  have [ident inj] [":", expr function.injective (int.cast_ring_hom exprℚ())] [],
  { intros [ident m, ident n],
    exact [expr int.cast_inj.mp] },
  apply [expr inj],
  rw ["[", "<-", expr constant_coeff_map, ",", expr map_witt_structure_int, ",", expr constant_coeff_witt_structure_rat, ",", expr ring_hom.map_zero, "]"] [],
  rw ["[", expr constant_coeff_map, ",", expr h, ",", expr ring_hom.map_zero, "]"] []
end

variable(R)

theorem witt_structure_rat_vars [Fintype idx] (Φ : MvPolynomial idx ℚ) (n : ℕ) :
  (wittStructureRat p Φ n).vars ⊆ Finset.univ.product (Finset.range (n+1)) :=
  by 
    rw [wittStructureRat]
    intro x hx 
    simp only [Finset.mem_product, true_andₓ, Finset.mem_univ, Finset.mem_range]
    obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx 
    obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx' 
    obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx'' 
    rw [witt_polynomial_vars, Finset.mem_range] at hj 
    replace hk := X_in_terms_of_W_vars_subset p _ hk 
    rw [Finset.mem_range] at hk 
    exact lt_of_lt_of_leₓ hj hk

-- error in RingTheory.WittVector.StructurePolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem witt_structure_int_vars
[fintype idx]
(Φ : mv_polynomial idx exprℤ())
(n : exprℕ()) : «expr ⊆ »((witt_structure_int p Φ n).vars, finset.univ.product (finset.range «expr + »(n, 1))) :=
begin
  have [] [":", expr function.injective (int.cast_ring_hom exprℚ())] [":=", expr int.cast_injective],
  rw ["[", "<-", expr vars_map_of_injective _ this, ",", expr map_witt_structure_int, "]"] [],
  apply [expr witt_structure_rat_vars]
end

end PPrime

