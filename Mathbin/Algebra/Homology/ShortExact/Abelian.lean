/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import Mathbin.Algebra.Homology.ShortExact.Preadditive
import Mathbin.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Short exact sequences in abelian categories

In an abelian category, a left-split short exact sequence admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type _} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}

variable [Abelian 𝒜]

open ZeroObject

theorem is_iso_of_short_exact_of_is_iso_of_is_iso (h : ShortExact f g) (h' : ShortExact f' g') (i₁ : A ⟶ A')
    (i₂ : B ⟶ B') (i₃ : C ⟶ C') (comm₁ : i₁ ≫ f' = f ≫ i₂) (comm₂ : i₂ ≫ g' = g ≫ i₃) [IsIso i₁] [IsIso i₃] :
    IsIso i₂ := by
  obtain ⟨_, _, _⟩ := h
  obtain ⟨_, _, _⟩ := h'
  skip
  refine'
      @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso 𝒜 _ _ 0 _ _ _ 0 _ _ _ 0 f g 0 f' g' 0 i₁ i₂ i₃ _ comm₁
        comm₂ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ <;>
    try
        simp <;>
      try
          apply exact_zero_left_of_mono <;>
        try
            assumption <;>
          rwa [← epi_iff_exact_zero_right]

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `biprod.inl : A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is than automatically an isomorphism. -/
-- TODO: we may also want the version that supplies a morphism `A ⊞ C ⟶ B`.
def Splitting.mk' (h : ShortExact f g) (i : B ⟶ A ⊞ C) (h1 : f ≫ i = biprod.inl) (h2 : i ≫ biprod.snd = g) :
    Splitting f g where
  Iso := by
    refine' @as_iso _ _ _ _ i (id _)
    refine'
      is_iso_of_short_exact_of_is_iso_of_is_iso h _ _ _ _ (h1.trans (category.id_comp _).symm).symm
        (h2.trans (category.comp_id _).symm)
    constructor
    apply exact_inl_snd
  comp_iso_eq_inl := by
    rwa [as_iso_hom]
  iso_comp_snd_eq := h2

/-- A short exact sequence that is left split admits a splitting. -/
def LeftSplit.splitting {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : Splitting f g :=
  Splitting.mk' h.ShortExact (biprod.lift h.LeftSplit.some g)
    (by
      ext
      · simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.left_split.some_spec
        
      · simp only [biprod.inl_snd, biprod.lift_snd, category.assoc, h.exact.w]
        )
    (by
      simp only [biprod.lift_snd])

end CategoryTheory

