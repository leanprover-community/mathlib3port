import Mathbin.RingTheory.Adjoin.Basic 
import Mathbin.RingTheory.PowerBasis

/-!
# Power basis for `algebra.adjoin R {x}`

This file defines the canonical power basis on `algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/


variable{K S : Type _}[Field K][CommRingₓ S][Algebra K S]

namespace Algebra

open Polynomial

open PowerBasis

open_locale BigOperators

-- error in RingTheory.Adjoin.PowerBasis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable
def adjoin.power_basis_aux
{x : S}
(hx : _root_.is_integral K x) : basis (fin (minpoly K x).nat_degree) K (adjoin K ({x} : set S)) :=
begin
  have [ident hST] [":", expr function.injective (algebra_map (adjoin K ({x} : set S)) S)] [":=", expr subtype.coe_injective],
  have [ident hx'] [":", expr _root_.is_integral K (show adjoin K ({x} : set S), from ⟨x, subset_adjoin (set.mem_singleton x)⟩)] [],
  { apply [expr (is_integral_algebra_map_iff hST).mp],
    convert [] [expr hx] [],
    apply_instance },
  have [ident minpoly_eq] [] [":=", expr minpoly.eq_of_algebra_map_eq hST hx' rfl],
  apply [expr @basis.mk (fin (minpoly K x).nat_degree) _ (adjoin K {x}) (λ
    i, «expr ^ »(⟨x, subset_adjoin (set.mem_singleton x)⟩, (i : exprℕ())))],
  { have [] [] [":=", expr hx'.linear_independent_pow],
    rwa [expr minpoly_eq] ["at", ident this] },
  { rw [expr _root_.eq_top_iff] [],
    rintros ["⟨", ident y, ",", ident hy, "⟩", "_"],
    have [] [] [":=", expr hx'.mem_span_pow],
    rw [expr minpoly_eq] ["at", ident this],
    apply [expr this],
    { rw ["[", expr adjoin_singleton_eq_range_aeval, "]"] ["at", ident hy],
      obtain ["⟨", ident f, ",", ident rfl, "⟩", ":=", expr (aeval x).mem_range.mp hy],
      use [expr f],
      ext [] [] [],
      exact [expr (is_scalar_tower.algebra_map_aeval K (adjoin K {x}) S ⟨x, _⟩ _).symm] } }
end

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.power_basis {x : S} (hx : _root_.is_integral K x) : PowerBasis K (adjoin K ({x} : Set S)) :=
  { gen := ⟨x, subset_adjoin (Set.mem_singleton x)⟩, dim := (minpoly K x).natDegree, Basis := adjoin.power_basis_aux hx,
    basis_eq_pow := Basis.mk_apply _ _ }

end Algebra

