import Mathbin.Algebra.Category.Module.EpiMono 
import Mathbin.Algebra.Module.Projective 
import Mathbin.CategoryTheory.Preadditive.Projective 
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# The category of `R`-modules has enough projectives.
-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open_locale ModuleCat

-- error in Algebra.Category.Module.Projective: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
theorem is_projective.iff_projective
{R : Type u}
[ring R]
{P : Type max u v}
[add_comm_group P]
[module R P] : «expr ↔ »(module.projective R P, projective (Module.of R P)) :=
begin
  refine [expr ⟨λ h, _, λ h, _⟩],
  { letI [] [":", expr module.projective R «expr↥ »(Module.of R P)] [":=", expr h],
    exact [expr ⟨λ E X f e epi, module.projective_lifting_property _ _ ((Module.epi_iff_surjective _).mp epi)⟩] },
  { refine [expr module.projective_of_lifting_property _],
    introsI [ident E, ident X, ident mE, ident mX, ident sE, ident sX, ident f, ident g, ident s],
    haveI [] [":", expr epi «expr↟ »(f)] [":=", expr (Module.epi_iff_surjective «expr↟ »(f)).mpr s],
    letI [] [":", expr projective (Module.of R P)] [":=", expr h],
    exact [expr ⟨projective.factor_thru «expr↟ »(g) «expr↟ »(f), projective.factor_thru_comp «expr↟ »(g) «expr↟ »(f)⟩] }
end

namespace ModuleCat

variable{R : Type u}[Ringₓ R]{M : ModuleCat.{max u v} R}

/-- Modules that have a basis are projective. -/
theorem projective_of_free {ι : Type _} (b : Basis ι R M) : projective M :=
  projective.of_iso (ModuleCat.ofSelfIso _) (IsProjective.iff_projective.mp (Module.projective_of_basis b))

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance Module_enough_projectives : enough_projectives (ModuleCat.{max u v} R) :=
  { presentation :=
      fun M =>
        ⟨{ P := ModuleCat.of R (M →₀ R), Projective := projective_of_free Finsupp.basisSingleOne,
            f := Finsupp.basisSingleOne.constr ℕ id,
            Epi :=
              (epi_iff_range_eq_top _).mpr
                (range_eq_top.2
                  fun m =>
                    ⟨Finsupp.single m (1 : R),
                      by 
                        simp [Basis.constr]⟩) }⟩ }

end ModuleCat

