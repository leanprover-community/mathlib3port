import Mathbin.Algebra.Group.Ext 
import Mathbin.CategoryTheory.Simple 
import Mathbin.CategoryTheory.Linear.Default 
import Mathbin.CategoryTheory.Endomorphism 
import Mathbin.FieldTheory.IsAlgClosed.Basic

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.

## Future work
It might be nice to provide a `division_ring` instance on `End X` when `X` is simple.
This is an easy consequence of the results here,
but may take some care setting up usable instances.
-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v u

variable{C : Type u}[category.{v} C]

variable[preadditive C]

-- error in CategoryTheory.Preadditive.Schur: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
theorem is_iso_of_hom_simple
[has_kernels C]
{X Y : C}
[simple X]
[simple Y]
{f : «expr ⟶ »(X, Y)}
(w : «expr ≠ »(f, 0)) : is_iso f :=
begin
  haveI [] [":", expr mono f] [":=", expr preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)],
  exact [expr is_iso_of_mono_of_nonzero w]
end

/--
As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
theorem is_iso_iff_nonzero [has_kernels C] {X Y : C} [simple.{v} X] [simple.{v} Y] (f : X ⟶ Y) : is_iso.{v} f ↔ f ≠ 0 :=
  ⟨fun I =>
      by 
        intro h 
        apply id_nonzero X 
        simp only [←is_iso.hom_inv_id f, h, zero_comp],
    fun w => is_iso_of_hom_simple w⟩

open FiniteDimensional

variable(𝕜 : Type _)[Field 𝕜]

-- error in CategoryTheory.Preadditive.Schur: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Part of **Schur's lemma** for `𝕜`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
theorem finrank_hom_simple_simple_eq_zero_of_not_iso
[has_kernels C]
[linear 𝕜 C]
{X Y : C}
[simple.{v} X]
[simple.{v} Y]
(h : «expr ≅ »(X, Y) → false) : «expr = »(finrank 𝕜 «expr ⟶ »(X, Y), 0) :=
begin
  haveI [] [] [":=", expr subsingleton_of_forall_eq (0 : «expr ⟶ »(X, Y)) (λ f, begin
      have [ident p] [] [":=", expr not_congr (is_iso_iff_nonzero f)],
      simp [] [] ["only"] ["[", expr not_not, ",", expr ne.def, "]"] [] ["at", ident p],
      refine [expr p.mp (λ _, by exactI [expr h (as_iso f)])]
    end)],
  exact [expr finrank_zero_of_subsingleton]
end

variable[IsAlgClosed 𝕜][linear 𝕜 C]

attribute [local ext] Module DistribMulAction MulAction HasScalar

-- error in CategoryTheory.Preadditive.Schur: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An auxiliary lemma for Schur's lemma.

If `X ⟶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X ⟶ X` is 1-dimensional.
-/
theorem finrank_endomorphism_eq_one
{X : C}
(is_iso_iff_nonzero : ∀ f : «expr ⟶ »(X, X), «expr ↔ »(is_iso f, «expr ≠ »(f, 0)))
[I : finite_dimensional 𝕜 «expr ⟶ »(X, X)] : «expr = »(finrank 𝕜 «expr ⟶ »(X, X), 1) :=
begin
  have [ident id_nonzero] [] [":=", expr (is_iso_iff_nonzero («expr𝟙»() X)).mp (by apply_instance)],
  apply [expr finrank_eq_one («expr𝟙»() X)],
  { exact [expr id_nonzero] },
  { intro [ident f],
    haveI [] [":", expr nontrivial (End X)] [":=", expr nontrivial_of_ne _ _ id_nonzero],
    obtain ["⟨", ident c, ",", ident nu, "⟩", ":=", expr @exists_spectrum_of_is_alg_closed_of_finite_dimensional 𝕜 _ _ (End X) _ _ _ (by { convert [] [expr I] [],
        ext [] [] [],
        refl,
        ext [] [] [],
        refl }) (End.of f)],
    use [expr c],
    rw ["[", expr is_unit_iff_is_iso, ",", expr is_iso_iff_nonzero, ",", expr ne.def, ",", expr not_not, ",", expr sub_eq_zero, ",", expr algebra.algebra_map_eq_smul_one, "]"] ["at", ident nu],
    exact [expr nu.symm] }
end

variable[has_kernels C]

/--
**Schur's lemma** for endomorphisms in `𝕜`-linear categories.
-/
theorem finrank_endomorphism_simple_eq_one (X : C) [simple.{v} X] [I : FiniteDimensional 𝕜 (X ⟶ X)] :
  finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_eq_one 𝕜 is_iso_iff_nonzero

theorem endomorphism_simple_eq_smul_id {X : C} [simple.{v} X] [I : FiniteDimensional 𝕜 (X ⟶ X)] (f : X ⟶ X) :
  ∃ c : 𝕜, c • 𝟙 X = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X) f

-- error in CategoryTheory.Preadditive.Schur: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
**Schur's lemma** for `𝕜`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
theorem finrank_hom_simple_simple_le_one
(X Y : C)
[∀ X Y : C, finite_dimensional 𝕜 «expr ⟶ »(X, Y)]
[simple.{v} X]
[simple.{v} Y] : «expr ≤ »(finrank 𝕜 «expr ⟶ »(X, Y), 1) :=
begin
  cases [expr subsingleton_or_nontrivial «expr ⟶ »(X, Y)] ["with", ident h],
  { resetI,
    convert [] [expr zero_le_one] [],
    exact [expr finrank_zero_of_subsingleton] },
  { obtain ["⟨", ident f, ",", ident nz, "⟩", ":=", expr (nontrivial_iff_exists_ne 0).mp h],
    haveI [ident fi] [] [":=", expr (is_iso_iff_nonzero f).mpr nz],
    apply [expr finrank_le_one f],
    intro [ident g],
    obtain ["⟨", ident c, ",", ident w, "⟩", ":=", expr endomorphism_simple_eq_smul_id 𝕜 «expr ≫ »(g, inv f)],
    exact [expr ⟨c, by simpa [] [] [] [] [] ["using", expr «expr =≫ »(w, f)]⟩] }
end

-- error in CategoryTheory.Preadditive.Schur: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finrank_hom_simple_simple_eq_one_iff
(X Y : C)
[∀ X Y : C, finite_dimensional 𝕜 «expr ⟶ »(X, Y)]
[simple.{v} X]
[simple.{v} Y] : «expr ↔ »(«expr = »(finrank 𝕜 «expr ⟶ »(X, Y), 1), nonempty «expr ≅ »(X, Y)) :=
begin
  fsplit,
  { intro [ident h],
    rw [expr finrank_eq_one_iff'] ["at", ident h],
    obtain ["⟨", ident f, ",", ident nz, ",", "-", "⟩", ":=", expr h],
    rw ["<-", expr is_iso_iff_nonzero] ["at", ident nz],
    exactI [expr ⟨as_iso f⟩] },
  { rintro ["⟨", ident f, "⟩"],
    have [ident le_one] [] [":=", expr finrank_hom_simple_simple_le_one 𝕜 X Y],
    have [ident zero_lt] [":", expr «expr < »(0, finrank 𝕜 «expr ⟶ »(X, Y))] [":=", expr finrank_pos_iff_exists_ne_zero.mpr ⟨f.hom, (is_iso_iff_nonzero f.hom).mp infer_instance⟩],
    linarith [] [] [] }
end

-- error in CategoryTheory.Preadditive.Schur: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finrank_hom_simple_simple_eq_zero_iff
(X Y : C)
[∀ X Y : C, finite_dimensional 𝕜 «expr ⟶ »(X, Y)]
[simple.{v} X]
[simple.{v} Y] : «expr ↔ »(«expr = »(finrank 𝕜 «expr ⟶ »(X, Y), 0), is_empty «expr ≅ »(X, Y)) :=
begin
  rw ["[", "<-", expr not_nonempty_iff, ",", "<-", expr not_congr (finrank_hom_simple_simple_eq_one_iff 𝕜 X Y), "]"] [],
  refine [expr ⟨λ h, by { rw [expr h] [], simp [] [] [] [] [] [] }, λ h, _⟩],
  have [] [] [":=", expr finrank_hom_simple_simple_le_one 𝕜 X Y],
  interval_cases [expr finrank 𝕜 «expr ⟶ »(X, Y)] [] ["with", ident h'],
  { exact [expr h'] },
  { exact [expr false.elim (h h')] }
end

end CategoryTheory

