/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang, Pierre-Alexandre Bazin
-/
import Mathbin.Algebra.Homology.ShortExact.Preadditive
import Mathbin.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# Short exact sequences in abelian categories

In an abelian category, a left-split or right-split short exact sequence admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {ð : Type _} [Category ð]

namespace CategoryTheory

variable {A B C A' B' C' : ð} {f : A â¶ B} {g : B â¶ C} {f' : A' â¶ B'} {g' : B' â¶ C'}

variable [Abelian ð]

open ZeroObject

theorem is_iso_of_short_exact_of_is_iso_of_is_iso (h : ShortExact f g) (h' : ShortExact f' g') (iâ : A â¶ A')
    (iâ : B â¶ B') (iâ : C â¶ C') (commâ : iâ â« f' = f â« iâ) (commâ : iâ â« g' = g â« iâ) [IsIso iâ] [IsIso iâ] :
    IsIso iâ := by
  obtain â¨_, _, _â© := h
  obtain â¨_, _, _â© := h'
  skip
  refine'
      @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso ð _ _ 0 _ _ _ 0 _ _ _ 0 f g 0 f' g' 0 iâ iâ iâ _ commâ
        commâ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _ <;>
    try
        simp <;>
      try
          apply exact_zero_left_of_mono <;>
        try
            assumption <;>
          rwa [â epi_iff_exact_zero_right]

/-- To construct a splitting of `A -fâ¶ B -gâ¶ C` it suffices to supply
a *morphism* `i : B â¶ A â C` such that `f â« i` is the canonical map `biprod.inl : A â¶ A â C` and
`i â« q = g`, where `q` is the canonical map `biprod.snd : A â C â¶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def Splitting.mk' (h : ShortExact f g) (i : B â¶ A â C) (h1 : f â« i = biprod.inl) (h2 : i â« biprod.snd = g) :
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

/-- To construct a splitting of `A -fâ¶ B -gâ¶ C` it suffices to supply
a *morphism* `i : A â C â¶ B` such that `p â« i = f` where `p` is the canonical map
`biprod.inl : A â¶ A â C`, and `i â« g` is the canonical map `biprod.snd : A â C â¶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def Splitting.mk'' (h : ShortExact f g) (i : A â C â¶ B) (h1 : biprod.inl â« i = f) (h2 : i â« g = biprod.snd) :
    Splitting f g where
  Iso := by
    refine' (@as_iso _ _ _ _ i (id _)).symm
    refine'
      is_iso_of_short_exact_of_is_iso_of_is_iso _ h _ _ _ (h1.trans (category.id_comp _).symm).symm
        (h2.trans (category.comp_id _).symm)
    constructor
    apply exact_inl_snd
  comp_iso_eq_inl := by
    rw [iso.symm_hom, as_iso_inv, is_iso.comp_inv_eq, h1]
  iso_comp_snd_eq := by
    rw [iso.symm_hom, as_iso_inv, is_iso.inv_comp_eq, h2]

/-- A short exact sequence that is left split admits a splitting. -/
def LeftSplit.splitting {f : A â¶ B} {g : B â¶ C} (h : LeftSplit f g) : Splitting f g :=
  Splitting.mk' h.ShortExact (biprod.lift h.LeftSplit.some g)
    (by
      ext
      Â· simpa only [â biprod.inl_fst, â biprod.lift_fst, â category.assoc] using h.left_split.some_spec
        
      Â· simp only [â biprod.inl_snd, â biprod.lift_snd, â category.assoc, â h.exact.w]
        )
    (by
      simp only [â biprod.lift_snd])

/-- A short exact sequence that is right split admits a splitting. -/
def RightSplit.splitting {f : A â¶ B} {g : B â¶ C} (h : RightSplit f g) : Splitting f g :=
  Splitting.mk'' h.ShortExact (biprod.desc f h.RightSplit.some) (biprod.inl_desc _ _)
    (by
      ext
      Â· rw [biprod.inl_snd, â category.assoc, biprod.inl_desc, h.exact.w]
        
      Â· rw [biprod.inr_snd, â category.assoc, biprod.inr_desc, h.right_split.some_spec]
        )

end CategoryTheory

