import Mathbin.Data.MvPolynomial.Cardinal 
import Mathbin.Data.MvPolynomial.Equiv

/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `polynomial R` is at most the maximum
of `#R` and `ω`.
-/


universe u

open_locale Cardinal

open Cardinal

namespace Polynomial

-- error in Data.Polynomial.Cardinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cardinal_mk_le_max
{R : Type u}
[comm_semiring R] : «expr ≤ »(«expr#»() (polynomial R), max («expr#»() R) exprω()) :=
calc
  «expr = »(«expr#»() (polynomial R), «expr#»() (mv_polynomial punit.{u+1} R)) : cardinal.eq.2 ⟨(mv_polynomial.punit_alg_equiv.{u, u} R).to_equiv.symm⟩
  «expr ≤ »(..., _) : mv_polynomial.cardinal_mk_le_max
  «expr ≤ »(..., _) : begin
    have [] [":", expr «expr ≤ »(«expr#»() punit.{u+1}, exprω())] [],
    from [expr le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩)],
    rw ["[", expr max_assoc, ",", expr max_eq_right this, "]"] []
  end

end Polynomial

