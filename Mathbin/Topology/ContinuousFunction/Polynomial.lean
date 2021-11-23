import Mathbin.Topology.Algebra.Polynomial 
import Mathbin.Topology.ContinuousFunction.Algebra 
import Mathbin.Topology.ContinuousFunction.Compact 
import Mathbin.Topology.UnitInterval

/-!
# Constructions relating polynomial functions and continuous functions.

## Main definitions

* `polynomial.to_continuous_map_on p X`: for `X : set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `polynomial.to_continuous_map_on_alg_hom`: the same, as an `R`-algebra homomorphism.
* `polynomial_functions (X : set R) : subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomial_functions_separates_points (X : set R) : (polynomial_functions X).separates_points`:
  the polynomial functions separate points.

-/


variable{R : Type _}

namespace Polynomial

section 

variable[Semiringₓ R][TopologicalSpace R][TopologicalRing R]

/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def to_continuous_map (p : Polynomial R) : C(R, R) :=
  ⟨fun x : R => p.eval x,
    by 
      continuity⟩

/--
A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def to_continuous_map_on (p : Polynomial R) (X : Set R) : C(X, R) :=
  ⟨fun x : X => p.to_continuous_map x,
    by 
      continuity⟩

end 

section 

variable{α : Type _}[TopologicalSpace α][CommSemiringₓ R][TopologicalSpace R][TopologicalRing R]

@[simp]
theorem aeval_continuous_map_apply (g : Polynomial R) (f : C(α, R)) (x : α) :
  ((Polynomial.aeval f) g) x = g.eval (f x) :=
  by 
    apply Polynomial.induction_on' g
    ·
      intro p q hp hq 
      simp [hp, hq]
    ·
      intro n a 
      simp [Pi.pow_apply f x n]

end 

section 

noncomputable theory

variable[CommSemiringₓ R][TopologicalSpace R][TopologicalRing R]

/--
The algebra map from `polynomial R` to continuous functions `C(R, R)`.
-/
@[simps]
def to_continuous_map_alg_hom : Polynomial R →ₐ[R] C(R, R) :=
  { toFun := fun p => p.to_continuous_map,
    map_zero' :=
      by 
        ext 
        simp ,
    map_add' :=
      by 
        intros 
        ext 
        simp ,
    map_one' :=
      by 
        ext 
        simp ,
    map_mul' :=
      by 
        intros 
        ext 
        simp ,
    commutes' :=
      by 
        intros 
        ext 
        simp [Algebra.algebra_map_eq_smul_one] }

/--
The algebra map from `polynomial R` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def to_continuous_map_on_alg_hom (X : Set R) : Polynomial R →ₐ[R] C(X, R) :=
  { toFun := fun p => p.to_continuous_map_on X,
    map_zero' :=
      by 
        ext 
        simp ,
    map_add' :=
      by 
        intros 
        ext 
        simp ,
    map_one' :=
      by 
        ext 
        simp ,
    map_mul' :=
      by 
        intros 
        ext 
        simp ,
    commutes' :=
      by 
        intros 
        ext 
        simp [Algebra.algebra_map_eq_smul_one] }

end 

end Polynomial

section 

variable[CommSemiringₓ R][TopologicalSpace R][TopologicalRing R]

/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological ring `R`.
-/
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R (Polynomial R)).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]
theorem polynomial_functions_coe (X : Set R) :
  (polynomialFunctions X : Set C(X, R)) = Set.Range (Polynomial.toContinuousMapOnAlgHom X) :=
  by 
    ext 
    simp [polynomialFunctions]

theorem polynomial_functions_separates_points (X : Set R) : (polynomialFunctions X).SeparatesPoints :=
  fun x y h =>
    by 
      refine' ⟨_, ⟨⟨_, ⟨⟨Polynomial.x, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩
      dsimp 
      simp only [Polynomial.eval_X]
      exact fun h' => h (Subtype.ext h')

open_locale UnitInterval

open ContinuousMap

-- error in Topology.ContinuousFunction.Polynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
theorem polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo_I
(a b : exprℝ())
(h : «expr < »(a, b)) : «expr = »((polynomial_functions exprI()).comap' (comp_right_alg_hom exprℝ() (Icc_homeo_I a b h).symm.to_continuous_map), polynomial_functions (set.Icc a b)) :=
begin
  ext [] [ident f] [],
  fsplit,
  { rintro ["⟨", ident p, ",", "⟨", "-", ",", ident w, "⟩", "⟩"],
    rw [expr continuous_map.ext_iff] ["at", ident w],
    dsimp [] [] [] ["at", ident w],
    let [ident q] [] [":=", expr p.comp «expr + »(«expr • »(«expr ⁻¹»(«expr - »(b, a)), polynomial.X), polynomial.C «expr * »(«expr- »(a), «expr ⁻¹»(«expr - »(b, a))))],
    refine [expr ⟨q, ⟨_, _⟩⟩],
    { simp [] [] [] [] [] [] },
    { ext [] [ident x] [],
      simp [] [] ["only"] ["[", expr neg_mul_eq_neg_mul_symm, ",", expr ring_hom.map_neg, ",", expr ring_hom.map_mul, ",", expr alg_hom.coe_to_ring_hom, ",", expr polynomial.eval_X, ",", expr polynomial.eval_neg, ",", expr polynomial.eval_C, ",", expr polynomial.eval_smul, ",", expr polynomial.eval_mul, ",", expr polynomial.eval_add, ",", expr polynomial.coe_aeval_eq_eval, ",", expr polynomial.eval_comp, ",", expr polynomial.to_continuous_map_on_alg_hom_apply, ",", expr polynomial.to_continuous_map_on_to_fun, ",", expr polynomial.to_continuous_map_to_fun, "]"] [] [],
      convert [] [expr w ⟨_, _⟩] []; clear [ident w],
      { change [expr «expr = »(x, (Icc_homeo_I a b h).symm ⟨«expr + »(_, _), _⟩)] [] [],
        ext [] [] [],
        simp [] [] ["only"] ["[", expr Icc_homeo_I_symm_apply_coe, ",", expr subtype.coe_mk, "]"] [] [],
        replace [ident h] [":", expr «expr ≠ »(«expr - »(b, a), 0)] [":=", expr sub_ne_zero_of_ne h.ne.symm],
        simp [] [] ["only"] ["[", expr mul_add, "]"] [] [],
        field_simp [] [] [] [],
        ring [] },
      { change [expr «expr ∈ »(«expr + »(_, _), exprI())] [] [],
        rw ["[", expr mul_comm «expr ⁻¹»(«expr - »(b, a)), ",", "<-", expr neg_mul_eq_neg_mul_symm, ",", "<-", expr add_mul, ",", "<-", expr sub_eq_add_neg, "]"] [],
        have [ident w₁] [":", expr «expr < »(0, «expr ⁻¹»(«expr - »(b, a)))] [":=", expr inv_pos.mpr (sub_pos.mpr h)],
        have [ident w₂] [":", expr «expr ≤ »(0, «expr - »((x : exprℝ()), a))] [":=", expr sub_nonneg.mpr x.2.1],
        have [ident w₃] [":", expr «expr ≤ »(«expr - »((x : exprℝ()), a), «expr - »(b, a))] [":=", expr sub_le_sub_right x.2.2 a],
        fsplit,
        { exact [expr mul_nonneg w₂ (le_of_lt w₁)] },
        { rw ["[", "<-", expr div_eq_mul_inv, ",", expr div_le_one (sub_pos.mpr h), "]"] [],
          exact [expr w₃] } } } },
  { rintro ["⟨", ident p, ",", "⟨", "-", ",", ident rfl, "⟩", "⟩"],
    let [ident q] [] [":=", expr p.comp «expr + »(«expr • »(«expr - »(b, a), polynomial.X), polynomial.C a)],
    refine [expr ⟨q, ⟨_, _⟩⟩],
    { simp [] [] [] [] [] [] },
    { ext [] [ident x] [],
      simp [] [] [] ["[", expr mul_comm, "]"] [] [] } }
end

end 

