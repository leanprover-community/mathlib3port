import Mathbin.Algebra.DirectSum.Module 
import Mathbin.Data.Finsupp.ToDfinsupp

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.
-/


universe u v w

noncomputable theory

open_locale DirectSum

open LinearMap Submodule

variable{R : Type u}{M : Type v}[Ringₓ R][AddCommGroupₓ M][Module R M]

section finsuppLequivDirectSum

variable(R M)(ι : Type _)[DecidableEq ι]

-- error in Algebra.DirectSum.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsupp_lequiv_direct_sum : «expr ≃ₗ[ ] »(«expr →₀ »(ι, M), R, «expr⨁ , »((i : ι), M)) :=
by haveI [] [":", expr ∀
 m : M, decidable «expr ≠ »(m, 0)] [":=", expr classical.dec_pred _]; exact [expr finsupp_lequiv_dfinsupp R]

@[simp]
theorem finsupp_lequiv_direct_sum_single (i : ι) (m : M) :
  finsuppLequivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.to_dfinsupp_single i m

-- error in Algebra.DirectSum.Finsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem finsupp_lequiv_direct_sum_symm_lof
(i : ι)
(m : M) : «expr = »((finsupp_lequiv_direct_sum R M ι).symm (direct_sum.lof R ι _ i m), finsupp.single i m) :=
begin
  letI [] [":", expr ∀ m : M, decidable «expr ≠ »(m, 0)] [":=", expr classical.dec_pred _],
  exact [expr dfinsupp.to_finsupp_single i m]
end

end finsuppLequivDirectSum

