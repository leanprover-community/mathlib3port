import Mathbin.CategoryTheory.Sites.DenseSubsite

/-!
# Induced Topology

We say that a functor `G : C ⥤ (D, K)` is locally dense if for each covering sieve `T` in `D` of
some `X : C`, `T ∩ mor(C)` generates a covering sieve of `X` in `D`. A locally dense fully faithful
functor then induces a topology on `C` via `{ T ∩ mor(C) | T ∈ K }`. Note that this is equal to
the collection of sieves on `C` whose image generates a covering sieve. This construction would
make `C` both cover-lifting and cover-preserving.

Some typical examples are full and cover-dense functors (for example the functor from a basis of a
topological space `X` into `opens X`). The functor `over X ⥤ C` is also locally dense, and the
induced topology can then be used to construct the big sites associated to a scheme.

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.induced_topology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/


namespace CategoryTheory

universe v u

open Limits Opposite Presieve

section

variable {C : Type _} [category C] {D : Type _} [category D] {G : C ⥤ D}

variable {J : grothendieck_topology C} {K : grothendieck_topology D}

variable (A : Type v) [category.{u} A]

/-- We say that a functor `C ⥤ D` into a site is "locally dense" if
for each covering sieve `T` in `D`, `T ∩ mor(C)` generates a covering sieve in `D`.
-/
def locally_cover_dense (K : grothendieck_topology D) (G : C ⥤ D) : Prop :=
  ∀ ⦃X⦄ T : K (G.obj X), (T.val.functor_pullback G).FunctorPushforward G ∈ K (G.obj X)

namespace LocallyCoverDense

variable [full G] [faithful G] (Hld : locally_cover_dense K G)

include Hld

theorem pushforward_cover_iff_cover_pullback {X : C} (S : sieve X) :
    K _ (S.functor_pushforward G) ↔ ∃ T : K (G.obj X), T.val.functor_pullback G = S := by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (sieve.fully_faithful_functor_galois_coinsertion G X).u_l_eq S⟩
    
  · rintro ⟨T, rfl⟩
    exact Hld T
    

/-- If a functor `G : C ⥤ (D, K)` is fully faithful and locally dense,
then the set `{ T ∩ mor(C) | T ∈ K }` is a grothendieck topology of `C`.
-/
@[simps]
def induced_topology : grothendieck_topology C where
  Sieves := fun X S => K _ (S.functor_pushforward G)
  top_mem' := fun X => by
    change K _ _
    rw [sieve.functor_pushforward_top]
    exact K.top_mem _
  pullback_stable' := fun X Y S f hS => by
    have : S.pullback f = ((S.functor_pushforward G).pullback (G.map f)).FunctorPullback G := by
      conv_lhs => rw [← (sieve.fully_faithful_functor_galois_coinsertion G X).u_l_eq S]
      ext
      change (S.functor_pushforward G) _ ↔ (S.functor_pushforward G) _
      rw [G.map_comp]
    rw [this]
    change K _ _
    apply Hld ⟨_, K.pullback_stable (G.map f) hS⟩
  transitive' := fun X S hS S' H' => by
    apply K.transitive hS
    rintro Y _ ⟨Z, g, i, hg, rfl⟩
    rw [sieve.pullback_comp]
    apply K.pullback_stable i
    refine' K.superset_covering _ (H' hg)
    rintro W _ ⟨Z', g', i', hg, rfl⟩
    use
      ⟨Z', g' ≫ g, i', hg, by
        simp ⟩

/-- `G` is cover-lifting wrt the induced topology. -/
theorem induced_topology_cover_lifting : cover_lifting Hld.induced_topology K G :=
  ⟨fun _ S hS => Hld ⟨S, hS⟩⟩

/-- `G` is cover-preserving wrt the induced topology. -/
theorem induced_topology_cover_preserving : cover_preserving Hld.induced_topology K G :=
  ⟨fun _ S hS => hS⟩

end LocallyCoverDense

theorem cover_dense.locally_cover_dense [full G] (H : cover_dense K G) : locally_cover_dense K G := by
  intro X T
  refine' K.superset_covering _ (K.bind_covering T.property fun Y f Hf => H.is_cover Y)
  rintro Y _ ⟨Z, _, f, hf, ⟨W, g, f', rfl : _ = _⟩, rfl⟩
  use W
  use G.preimage (f' ≫ f)
  use g
  constructor
  simpa using T.val.downward_closed hf f'
  simp

/-- Given a fully faithful cover-dense functor `G : C ⥤ (D, K)`, we may induce a topology on `C`.
-/
abbrev cover_dense.induced_topology [full G] [faithful G] (H : cover_dense K G) : grothendieck_topology C :=
  H.locally_cover_dense.induced_topology

variable (J)

theorem over_forget_locally_cover_dense (X : C) : locally_cover_dense J (over.forget X) := by
  intro Y T
  convert T.property
  ext Z f
  constructor
  · rintro ⟨_, _, g', hg, rfl⟩
    exact T.val.downward_closed hg g'
    
  · intro hf
    exact ⟨over.mk (f ≫ Y.hom), over.hom_mk f, 𝟙 _, hf, (category.id_comp _).symm⟩
    

end

section SmallSite

variable {C : Type v} [small_category C] {D : Type v} [small_category D] {G : C ⥤ D}

variable {J : grothendieck_topology C} {K : grothendieck_topology D}

variable (A : Type u) [category.{v} A]

/-- Cover-dense functors induces an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the value category
is complete.
-/
noncomputable def cover_dense.Sheaf_equiv [full G] [faithful G] (H : cover_dense K G) [has_limits A] :
    Sheaf H.induced_topology A ≌ Sheaf K A :=
  H.Sheaf_equiv_of_cover_preserving_cover_lifting H.locally_cover_dense.induced_topology_cover_preserving
    H.locally_cover_dense.induced_topology_cover_lifting

end SmallSite

end CategoryTheory

