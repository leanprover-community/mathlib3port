import Mathbin.CategoryTheory.Sites.Grothendieck

/-!
# Grothendieck pretopologies

Definition and lemmas about Grothendieck pretopologies.
A Grothendieck pretopology for a category `C` is a set of families of morphisms with fixed codomain,
satisfying certain closure conditions.

We show that a pretopology generates a genuine Grothendieck topology, and every topology has
a maximal pretopology which generates it.

The pretopology associated to a topological space is defined in `spaces.lean`.

## Tags

coverage, pretopology, site

## References

* [https://ncatlab.org/nlab/show/Grothendieck+pretopology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [https://stacks.math.columbia.edu/tag/00VG][Stacks]
-/


universe v u

noncomputable theory

namespace CategoryTheory

open CategoryTheory Category Limits Presieve

variable{C : Type u}[category.{v} C][has_pullbacks C]

variable(C)

/--
A (Grothendieck) pretopology on `C` consists of a collection of families of morphisms with a fixed
target `X` for every object `X` in `C`, called "coverings" of `X`, which satisfies the following
three axioms:
1. Every family consisting of a single isomorphism is a covering family.
2. The collection of covering families is stable under pullback.
3. Given a covering family, and a covering family on each domain of the former, the composition
   is a covering family.

In some sense, a pretopology can be seen as Grothendieck topology with weaker saturation conditions,
in that each covering is not necessarily downward closed.

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology, or
https://stacks.math.columbia.edu/tag/00VH, or [MM92] Chapter III, Section 2, Definition 2.
Note that Stacks calls a category together with a pretopology a site, and [MM92] calls this
a basis for a topology.
-/
@[ext]
structure pretopology where 
  Coverings : ∀ X : C, Set (presieve X)
  has_isos : ∀ ⦃X Y⦄ f : Y ⟶ X [is_iso f], presieve.singleton f ∈ coverings X 
  pullbacks : ∀ ⦃X Y⦄ f : Y ⟶ X S, S ∈ coverings X → pullback_arrows f S ∈ coverings Y 
  Transitive :
  ∀ ⦃X : C⦄ S : presieve X Ti : ∀ ⦃Y⦄ f : Y ⟶ X, S f → presieve Y,
    S ∈ coverings X → (∀ ⦃Y⦄ f H : S f, Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X

namespace Pretopology

instance  : CoeFun (pretopology C) fun _ => ∀ X : C, Set (presieve X) :=
  ⟨coverings⟩

instance  : PartialOrderₓ (pretopology C) :=
  { le := fun K₁ K₂ => (K₁ : ∀ X : C, Set _) ≤ K₂, le_refl := fun K => le_reflₓ _,
    le_trans := fun K₁ K₂ K₃ h₁₂ h₂₃ => le_transₓ h₁₂ h₂₃,
    le_antisymm := fun K₁ K₂ h₁₂ h₂₁ => pretopology.ext _ _ (le_antisymmₓ h₁₂ h₂₁) }

instance  : OrderTop (pretopology C) :=
  { top :=
      { Coverings := fun _ => Set.Univ, has_isos := fun _ _ _ _ => Set.mem_univ _,
        pullbacks := fun _ _ _ _ _ => Set.mem_univ _, Transitive := fun _ _ _ _ _ => Set.mem_univ _ },
    le_top := fun K X S hS => Set.mem_univ _ }

instance  : Inhabited (pretopology C) :=
  ⟨⊤⟩

/--
A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See https://stacks.math.columbia.edu/tag/00ZC, or [MM92] Chapter III, Section 2, Equation (2).
-/
def to_grothendieck (K : pretopology C) : grothendieck_topology C :=
  { Sieves := fun X S => ∃ (R : _)(_ : R ∈ K X), R ≤ (S : presieve _),
    top_mem' := fun X => ⟨presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩,
    pullback_stable' :=
      fun X Y S g =>
        by 
          rintro ⟨R, hR, RS⟩
          refine' ⟨_, K.pullbacks g _ hR, _⟩
          rw [←sieve.sets_iff_generate, sieve.pullback_arrows_comm]
          apply sieve.pullback_monotone 
          rwa [sieve.gi_generate.gc],
    transitive' :=
      by 
        rintro X S ⟨R', hR', RS⟩ R t 
        choose t₁ t₂ t₃ using t 
        refine' ⟨_, K.transitive _ _ hR' fun _ f hf => t₂ (RS _ hf), _⟩
        rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
        apply t₃ (RS _ hg) _ hf }

theorem mem_to_grothendieck (K : pretopology C) X S :
  S ∈ to_grothendieck C K X ↔ ∃ (R : _)(_ : R ∈ K X), R ≤ (S : presieve X) :=
  Iff.rfl

/--
The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def of_grothendieck (J : grothendieck_topology C) : pretopology C :=
  { Coverings := fun X R => sieve.generate R ∈ J X,
    has_isos :=
      fun X Y f i =>
        by 
          exactI
            J.covering_of_eq_top
              (by 
                simp ),
    pullbacks :=
      fun X Y f R hR =>
        by 
          rw [Set.mem_def, sieve.pullback_arrows_comm]
          apply J.pullback_stable f hR,
    Transitive :=
      fun X S Ti hS hTi =>
        by 
          apply J.transitive hS 
          intro Y f 
          rintro ⟨Z, g, f, hf, rfl⟩
          rw [sieve.pullback_comp]
          apply J.pullback_stable g 
          apply J.superset_covering _ (hTi _ hf)
          rintro Y g ⟨W, h, g, hg, rfl⟩
          exact
            ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩,
              by 
                simp ⟩ }

/-- We have a galois insertion from pretopologies to Grothendieck topologies. -/
def gi : GaloisInsertion (to_grothendieck C) (of_grothendieck C) :=
  { gc :=
      fun K J =>
        by 
          split 
          ·
            intro h X R hR 
            exact h _ ⟨_, hR, sieve.le_generate R⟩
          ·
            rintro h X S ⟨R, hR, RS⟩
            apply J.superset_covering _ (h _ hR)
            rwa [sieve.gi_generate.gc],
    le_l_u := fun J X S hS => ⟨S, J.superset_covering S.le_generate hS, le_reflₓ _⟩,
    choice := fun x hx => to_grothendieck C x, choice_eq := fun _ _ => rfl }

/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See https://stacks.math.columbia.edu/tag/07GE
-/
def trivialₓ : pretopology C :=
  { Coverings := fun X S => ∃ (Y : _)(f : Y ⟶ X)(h : is_iso f), S = presieve.singleton f,
    has_isos := fun X Y f i => ⟨_, _, i, rfl⟩,
    pullbacks :=
      fun X Y f S =>
        by 
          rintro ⟨Z, g, i, rfl⟩
          refine' ⟨pullback g f, pullback.snd, _, _⟩
          ·
            resetI 
            refine'
              ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _)
                    (by 
                      simp ),
                  ⟨_,
                    by 
                      tidy⟩⟩⟩
            apply pullback.hom_ext
            ·
              rw [assoc, pullback.lift_fst, ←pullback.condition_assoc]
              simp 
            ·
              simp 
          ·
            apply pullback_singleton,
    Transitive :=
      by 
        rintro X S Ti ⟨Z, g, i, rfl⟩ hS 
        rcases hS g (singleton_self g) with ⟨Y, f, i, hTi⟩
        refine' ⟨_, f ≫ g, _, _⟩
        ·
          resetI 
          infer_instance 
        ext W k 
        split 
        ·
          rintro ⟨V, h, k, ⟨_⟩, hh, rfl⟩
          rw [hTi] at hh 
          cases hh 
          apply singleton.mk
        ·
          rintro ⟨_⟩
          refine' bind_comp g presieve.singleton.mk _ 
          rw [hTi]
          apply presieve.singleton.mk }

instance  : OrderBot (pretopology C) :=
  { bot := trivialₓ C,
    bot_le :=
      fun K X R =>
        by 
          rintro ⟨Y, f, hf, rfl⟩
          exactI K.has_isos f }

/-- The trivial pretopology induces the trivial grothendieck topology. -/
theorem to_grothendieck_bot : to_grothendieck C ⊥ = ⊥ :=
  (gi C).gc.l_bot

end Pretopology

end CategoryTheory

