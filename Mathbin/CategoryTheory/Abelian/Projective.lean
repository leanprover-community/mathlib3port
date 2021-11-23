import Mathbin.CategoryTheory.Abelian.Exact 
import Mathbin.CategoryTheory.Preadditive.ProjectiveResolution

/-!
# Abelian categories with enough projectives have projective resolutions

When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
-/


noncomputable theory

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

open CategoryTheory.Projective

variable{C : Type u}[category.{v} C]

section 

variable[enough_projectives C][abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
theorem exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
  (abelian.exact_iff _ _).2$
    ⟨by 
        simp ,
      zero_of_epi_comp (π _)$
        by 
          rw [←category.assoc, cokernel.condition]⟩

end 

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `projective.syzygies`
applied to the previously constructed morphism,
and the map to the `n`-th object as `projective.d`.
-/


variable[abelian C][enough_projectives C]

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps]
def of_complex (Z : C) : ChainComplex C ℕ :=
  ChainComplex.mk' (projective.over Z) (projective.syzygies (projective.π Z)) (projective.d (projective.π Z))
    fun ⟨X, Y, f⟩ => ⟨projective.syzygies f, projective.d f, (exact_d_f f).w⟩

/--
In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projection resolution of the object `Z`.
-/
@[irreducible]
def of (Z : C) : ProjectiveResolution Z :=
  { complex := of_complex Z,
    π :=
      ChainComplex.mkHom _ _ (projective.π Z) 0
        (by 
          simp 
          exact (exact_d_f (projective.π Z)).w.symm)
        fun n _ =>
          ⟨0,
            by 
              ext⟩,
    Projective :=
      by 
        rintro (_ | _ | _ | n) <;> apply projective.projective_over,
    exact₀ :=
      by 
        simpa using exact_d_f (projective.π Z),
    exact :=
      by 
        rintro (_ | n) <;>
          ·
            simp 
            apply exact_d_f,
    Epi := projective.π_epi Z }

instance (priority := 100) (Z : C) : has_projective_resolution Z :=
  { out := ⟨of Z⟩ }

instance (priority := 100) : has_projective_resolutions C :=
  { out :=
      fun Z =>
        by 
          infer_instance }

end ProjectiveResolution

end CategoryTheory

