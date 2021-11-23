import Mathbin.Topology.Instances.RealVectorSpace 
import Mathbin.Analysis.NormedSpace.AffineIsometry 
import Mathbin.LinearAlgebra.AffineSpace.Midpoint

/-!
# Mazur-Ulam Theorem

Mazur-Ulam theorem states that an isometric bijection between two normed affine spaces over `ℝ` is
affine. We formalize it in three definitions:

* `isometric.to_real_linear_isometry_equiv_of_map_zero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃ₗᵢ[ℝ] F` with the same `to_fun` and `inv_fun`;
* `isometric.to_real_linear_isometry_equiv` : given `f : E ≃ᵢ F`, returns a linear isometry
  equivalence `g : E ≃ₗᵢ[ℝ] F` with `g x = f x - f 0`.
* `isometric.to_real_affine_isometry_equiv` : given `f : PE ≃ᵢ PF`, returns an affine isometry
  equivalence `g : PE ≃ᵃⁱ[ℝ] PF` whose underlying `isometric` is `f`

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/


variable{E PE :
    Type
      _}[NormedGroup
      E][NormedSpace ℝ
      E][MetricSpace
      PE][NormedAddTorsor E PE]{F PF : Type _}[NormedGroup F][NormedSpace ℝ F][MetricSpace PF][NormedAddTorsor F PF]

open Set AffineMap AffineIsometryEquiv

noncomputable theory

namespace Isometric

include E

-- error in Analysis.NormedSpace.MazurUlam: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
theorem midpoint_fixed
{x
 y : PE} : ∀
e : «expr ≃ᵢ »(PE, PE), «expr = »(e x, x) → «expr = »(e y, y) → «expr = »(e (midpoint exprℝ() x y), midpoint exprℝ() x y) :=
begin
  set [] [ident z] [] [":="] [expr midpoint exprℝ() x y] [],
  set [] [ident s] [] [":="] [expr {e : «expr ≃ᵢ »(PE, PE) | «expr ∧ »(«expr = »(e x, x), «expr = »(e y, y))}] [],
  haveI [] [":", expr nonempty s] [":=", expr ⟨⟨isometric.refl PE, rfl, rfl⟩⟩],
  have [ident h_bdd] [":", expr bdd_above «expr $ »(range, λ e : s, dist (e z) z)] [],
  { refine [expr ⟨«expr + »(dist x z, dist x z), «expr $ »(forall_range_iff.2, subtype.forall.2 _)⟩],
    rintro [ident e, "⟨", ident hx, ",", ident hy, "⟩"],
    calc
      «expr ≤ »(dist (e z) z, «expr + »(dist (e z) x, dist x z)) : dist_triangle (e z) x z
      «expr = »(..., «expr + »(dist (e x) (e z), dist x z)) : by rw ["[", expr hx, ",", expr dist_comm, "]"] []
      «expr = »(..., «expr + »(dist x z, dist x z)) : by erw ["[", expr e.dist_eq x z, "]"] [] },
  set [] [ident R] [":", expr «expr ≃ᵢ »(PE, PE)] [":="] [expr (point_reflection exprℝ() z).to_isometric] [],
  set [] [ident f] [":", expr «expr ≃ᵢ »(PE, PE) → «expr ≃ᵢ »(PE, PE)] [":="] [expr λ
   e, ((e.trans R).trans e.symm).trans R] [],
  have [ident hf_dist] [":", expr ∀ e, «expr = »(dist (f e z) z, «expr * »(2, dist (e z) z))] [],
  { intro [ident e],
    dsimp [] ["[", expr f, "]"] [] [],
    rw ["[", expr dist_point_reflection_fixed, ",", "<-", expr e.dist_eq, ",", expr e.apply_symm_apply, ",", expr dist_point_reflection_self_real, ",", expr dist_comm, "]"] [] },
  have [ident hf_maps_to] [":", expr maps_to f s s] [],
  { rintros [ident e, "⟨", ident hx, ",", ident hy, "⟩"],
    split; simp [] [] [] ["[", expr hx, ",", expr hy, ",", expr e.symm_apply_eq.2 hx.symm, ",", expr e.symm_apply_eq.2 hy.symm, "]"] [] [] },
  set [] [ident c] [] [":="] [expr «expr⨆ , »((e : s), dist ((e : «expr ≃ᵢ »(PE, PE)) z) z)] [],
  have [] [":", expr «expr ≤ »(c, «expr / »(c, 2))] [],
  { apply [expr csupr_le],
    rintros ["⟨", ident e, ",", ident he, "⟩"],
    simp [] [] ["only"] ["[", expr subtype.coe_mk, ",", expr le_div_iff' (@zero_lt_two exprℝ() _ _), ",", "<-", expr hf_dist, "]"] [] [],
    exact [expr le_csupr h_bdd ⟨f e, hf_maps_to he⟩] },
  replace [] [":", expr «expr ≤ »(c, 0)] [],
  { linarith [] [] [] },
  refine [expr λ e hx hy, dist_le_zero.1 (le_trans _ this)],
  exact [expr le_csupr h_bdd ⟨e, hx, hy⟩]
end

include F

-- error in Analysis.NormedSpace.MazurUlam: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A bijective isometry sends midpoints to midpoints. -/
theorem map_midpoint
(f : «expr ≃ᵢ »(PE, PF))
(x y : PE) : «expr = »(f (midpoint exprℝ() x y), midpoint exprℝ() (f x) (f y)) :=
begin
  set [] [ident e] [":", expr «expr ≃ᵢ »(PE, PE)] [":="] [expr («expr $ »(f.trans, «expr $ »(point_reflection exprℝ(), midpoint exprℝ() (f x) (f y)).to_isometric).trans f.symm).trans «expr $ »(point_reflection exprℝ(), midpoint exprℝ() x y).to_isometric] [],
  have [ident hx] [":", expr «expr = »(e x, x)] [],
  by simp [] [] [] [] [] [],
  have [ident hy] [":", expr «expr = »(e y, y)] [],
  by simp [] [] [] [] [] [],
  have [ident hm] [] [":=", expr e.midpoint_fixed hx hy],
  simp [] [] ["only"] ["[", expr e, ",", expr trans_apply, "]"] [] ["at", ident hm],
  rwa ["[", "<-", expr eq_symm_apply, ",", expr to_isometric_symm, ",", expr point_reflection_symm, ",", expr coe_to_isometric, ",", expr coe_to_isometric, ",", expr point_reflection_self, ",", expr symm_apply_eq, ",", expr point_reflection_fixed_iff, "]"] ["at", ident hm]
end

/-!
Since `f : PE ≃ᵢ PF` sends midpoints to midpoints, it is an affine map.
We define a conversion to a `continuous_linear_equiv` first, then a conversion to an `affine_map`.
-/


/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear isometry equivalence. -/
def to_real_linear_isometry_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) : E ≃ₗᵢ[ℝ] F :=
  { (AddMonoidHom.ofMapMidpoint ℝ ℝ f h0 f.map_midpoint).toRealLinearMap f.continuous, f with
    norm_map' :=
      fun x =>
        show ∥f x∥ = ∥x∥by 
          simp only [←dist_zero_right, ←h0, f.dist_eq] }

@[simp]
theorem coe_to_real_linear_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  «expr⇑ » (f.to_real_linear_isometry_equiv_of_map_zero h0) = f :=
  rfl

@[simp]
theorem coe_to_real_linear_equiv_of_map_zero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) :
  «expr⇑ » (f.to_real_linear_isometry_equiv_of_map_zero h0).symm = f.symm :=
  rfl

/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear isometry equivalence. -/
def to_real_linear_isometry_equiv (f : E ≃ᵢ F) : E ≃ₗᵢ[ℝ] F :=
  (f.trans (Isometric.addRight (f 0)).symm).toRealLinearIsometryEquivOfMapZero
    (by 
      simpa only [sub_eq_add_neg] using sub_self (f 0))

@[simp]
theorem to_real_linear_equiv_apply (f : E ≃ᵢ F) (x : E) : (f.to_real_linear_isometry_equiv : E → F) x = f x - f 0 :=
  (sub_eq_add_neg (f x) (f 0)).symm

@[simp]
theorem to_real_linear_isometry_equiv_symm_apply (f : E ≃ᵢ F) (y : F) :
  (f.to_real_linear_isometry_equiv.symm : F → E) y = f.symm (y+f 0) :=
  rfl

/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed add-torsors over
normed vector spaces over `ℝ`, then `f` is an affine isometry equivalence. -/
def to_real_affine_isometry_equiv (f : PE ≃ᵢ PF) : PE ≃ᵃⁱ[ℝ] PF :=
  AffineIsometryEquiv.mk' f
    ((vadd_const ℝ (Classical.arbitrary PE)).toIsometric.trans$
        f.trans (vadd_const ℝ (f$ Classical.arbitrary PE)).toIsometric.symm).toRealLinearIsometryEquiv
    (Classical.arbitrary PE)
    fun p =>
      by 
        simp 

@[simp]
theorem coe_fn_to_real_affine_isometry_equiv (f : PE ≃ᵢ PF) : «expr⇑ » f.to_real_affine_isometry_equiv = f :=
  rfl

@[simp]
theorem coe_to_real_affine_isometry_equiv (f : PE ≃ᵢ PF) : f.to_real_affine_isometry_equiv.to_isometric = f :=
  by 
    ext 
    rfl

end Isometric

