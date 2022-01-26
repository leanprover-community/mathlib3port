import Mathbin.AlgebraicTopology.SimplicialObject
import Mathbin.AlgebraicTopology.TopologicalSimplex
import Mathbin.CategoryTheory.Limits.Presheaf
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Yoneda
import Mathbin.Topology.Category.Top.Limits

/-!
A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

We define the standard simplices `Δ[n]` as simplicial sets,
and their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open_locale simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `fin n → fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.
-/


universe v u

open CategoryTheory

open_locale Simplicial

/-- The category of simplicial sets.
This is the category of contravariant functors from
`simplex_category` to `Type u`. -/
def SSet : Type (u + 1) :=
  simplicial_object (Type u)deriving large_category, limits.has_limits, limits.has_colimits

namespace SSet

/-- The `n`-th standard simplex `Δ[n]` associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standard_simplex : SimplexCategory ⥤ SSet :=
  yoneda

localized [Simplicial] notation "Δ[" n "]" => SSet.standardSimplex.obj (SimplexCategory.mk n)

instance : Inhabited SSet :=
  ⟨Δ[0]⟩

section

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `fin (m+1)` to `fin (n+1)`. -/
def as_order_hom {n} {m} (α : Δ[n].obj m) : OrderHom (Finₓ (m.unop.len + 1)) (Finₓ (n + 1)) :=
  α.to_order_hom

end

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : SSet where
  obj := fun m => { α : Δ[n].obj m // ¬Function.Surjective (as_order_hom α) }
  map := fun m₁ m₂ f α =>
    ⟨f.unop ≫ (α : Δ[n].obj m₁), by
      intro h
      apply α.property
      exact Function.Surjective.of_comp h⟩

localized [Simplicial] notation "∂Δ[" n "]" => SSet.boundary n

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundary_inclusion (n : ℕ) : ∂Δ[n] ⟶ Δ[n] where
  app := fun m α : { α : Δ[n].obj m // _ } => α

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : ℕ) (i : Finₓ (n + 1)) : SSet where
  obj := fun m => { α : Δ[n].obj m // Set.Range (as_order_hom α) ∪ {i} ≠ Set.Univ }
  map := fun m₁ m₂ f α =>
    ⟨f.unop ≫ (α : Δ[n].obj m₁), by
      intro h
      apply α.property
      rw [Set.eq_univ_iff_forall] at h⊢
      intro j
      apply Or.imp _ id (h j)
      intro hj
      exact Set.range_comp_subset_range _ _ hj⟩

localized [Simplicial] notation "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def horn_inclusion (n : ℕ) (i : Finₓ (n + 1)) : Λ[n, i] ⟶ Δ[n] where
  app := fun m α : { α : Δ[n].obj m // _ } => α

section Examples

open_locale Simplicial

/-- The simplicial circle. -/
noncomputable def S1 : SSet :=
  limits.colimit <|
    limits.parallel_pair (standard_simplex.map <| SimplexCategory.δ 0 : Δ[0] ⟶ Δ[1])
      (standard_simplex.map <| SimplexCategory.δ 1)

end Examples

/-- Truncated simplicial sets. -/
def truncated (n : ℕ) :=
  simplicial_object.truncated (Type u) n deriving large_category, limits.has_limits, limits.has_colimits

/-- The skeleton functor on simplicial sets. -/
def sk (n : ℕ) : SSet ⥤ SSet.Truncated n :=
  simplicial_object.sk n

instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(sk n).obj <| Δ[0]⟩

end SSet

/-- The functor associating the singular simplicial set to a topological space. -/
noncomputable def Top.toSSet : Top ⥤ SSet :=
  colimit_adj.restricted_yoneda SimplexCategory.toTop

/-- The geometric realization functor. -/
noncomputable def SSet.toTop : SSet ⥤ Top :=
  colimit_adj.extend_along_yoneda SimplexCategory.toTop

/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSetTopAdj : SSet.toTop ⊣ Top.toSSet :=
  colimit_adj.yoneda_adjunction _

/-- The geometric realization of the representable simplicial sets agree
  with the usual topological simplices. -/
noncomputable def SSet.toTopSimplex : (yoneda : SimplexCategory ⥤ _) ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  colimit_adj.is_extension_along_yoneda _

