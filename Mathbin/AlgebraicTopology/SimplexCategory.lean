/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathbin.CategoryTheory.Skeletal
import Mathbin.Tactic.Linarith.Default
import Mathbin.Data.Fintype.Sort
import Mathbin.Order.Category.NonemptyFinLinOrd
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `fin (n+1)` to `fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `simplex_category` and `simplex_category.hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `simplex_category.mk` creates an object of `simplex_category` out of a natural number.
  Use the notation `[n]` in the `simplicial` locale.
2. `simplex_category.len` gives the "length" of an object of `simplex_category`, as a natural.
3. `simplex_category.hom.mk` makes a morphism out of a monotone map between `fin`'s.
4. `simplex_category.hom.to_order_hom` gives the underlying monotone map associated to a
  term of `simplex_category.hom`.

-/


universe v

open CategoryTheory

-- ././Mathport/Syntax/Translate/Basic.lean:1200:31: unsupported: @[derive, irreducible] def
/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `fin (n+1) → fin (m+1)`
-/
irreducible_def SimplexCategory :=
  ℕ

namespace SimplexCategory

section

attribute [local semireducible] SimplexCategory

/-- Interpet a natural number as an object of the simplex category. -/
-- TODO: Make `mk` irreducible.
def mk (n : ℕ) : SimplexCategory :=
  n

-- mathport name: «expr[ ]»
localized [Simplicial] notation "[" n "]" => SimplexCategory.mk n

/-- The length of an object of `simplex_category`. -/
-- TODO: Make `len` irreducible.
def len (n : SimplexCategory) : ℕ :=
  n

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl

@[simp]
theorem mk_len (n : SimplexCategory) : [n.len] = n :=
  rfl

/-- Morphisms in the simplex_category. -/
@[nolint has_inhabited_instance]
protected irreducible_def Hom (a b : SimplexCategory) :=
  Finₓ (a.len + 1) →o Finₓ (b.len + 1)

namespace Hom

attribute [local semireducible] SimplexCategory.Hom

/-- Make a moprhism in `simplex_category` from a monotone map of fin's. -/
def mk {a b : SimplexCategory} (f : Finₓ (a.len + 1) →o Finₓ (b.len + 1)) : SimplexCategory.Hom a b :=
  f

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : Finₓ (a.len + 1) →o Finₓ (b.len + 1) :=
  f

@[ext]
theorem ext {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) : f.toOrderHom = g.toOrderHom → f = g :=
  id

@[simp]
theorem mk_to_order_hom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl

@[simp]
theorem to_order_hom_mk {a b : SimplexCategory} (f : Finₓ (a.len + 1) →o Finₓ (b.len + 1)) : (mk f).toOrderHom = f :=
  rfl

theorem mk_to_order_hom_apply {a b : SimplexCategory} (f : Finₓ (a.len + 1) →o Finₓ (b.len + 1))
    (i : Finₓ (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `simplex_category`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `simplex_category`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom := fun n m => SimplexCategory.Hom n m
  id := fun m => SimplexCategory.Hom.id _
  comp := fun _ _ _ f g => SimplexCategory.Hom.comp g f

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory) (i : Finₓ (x.len + 1)) : [0] ⟶ x :=
  hom.mk <|
    ⟨fun _ => i, by
      tauto⟩

@[simp]
theorem const_comp (x y : SimplexCategory) (i : Finₓ (x.len + 1)) (f : x ⟶ y) :
    const x i ≫ f = const y (f.toOrderHom i) :=
  rfl

/-- Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms beetween `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Finₓ (n + 1) →o Finₓ (m + 1)) : [n] ⟶ [m] :=
  SimplexCategory.Hom.mk f

theorem hom_zero_zero (f : [0] ⟶ [0]) : f = 𝟙 _ := by
  ext : 2
  dsimp'
  apply Subsingleton.elimₓ

end

open Simplicial

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/


/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : Finₓ (n + 2)) : [n] ⟶ [n + 1] :=
  mkHom (Finₓ.succAbove i).toOrderHom

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : Finₓ (n + 1)) : [n + 1] ⟶ [n] :=
  mkHom { toFun := Finₓ.predAbove i, monotone' := Finₓ.pred_above_right_monotone i }

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Finₓ (n + 2)} (H : i ≤ j) : δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ := by
  ext k
  dsimp' [δ, Finₓ.succAbove]
  simp only [OrderEmbedding.to_order_hom_coe, OrderEmbedding.coe_of_strict_mono, Function.comp_app,
    SimplexCategory.Hom.to_order_hom_mk, OrderHom.comp_coe]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;>
    · simp at * <;> linarith
      

/-- The special case of the first simplicial identity -/
theorem δ_comp_δ_self {n} {i : Finₓ (n + 2)} : δ i ≫ δ i.cast_succ = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_reflₓ i)).symm

/-- The second simplicial identity -/
theorem δ_comp_σ_of_le {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : i ≤ j.cast_succ) :
    δ i.cast_succ ≫ σ j.succ = σ j ≫ δ i := by
  ext k
  suffices
    ite (j.succ.cast_succ < ite (k < i) k.cast_succ k.succ) (ite (k < i) (k : ℕ) (k + 1) - 1) (ite (k < i) k (k + 1)) =
      ite
        ((if h : (j : ℕ) < k then
              k.pred
                (by
                  rintro rfl
                  exact Nat.not_lt_zeroₓ _ h)
            else
              k.cast_lt
                (by
                  cases j
                  cases k
                  simp only [len_mk]
                  linarith)).cast_succ <
          i)
        (ite (j.cast_succ < k) (k - 1) k) (ite (j.cast_succ < k) (k - 1) k + 1)
    by
    dsimp' [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
    simp' [Finₓ.predAbove] with push_cast
    convert rfl
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Subtype.mk_le_mk, Finₓ.cast_succ_mk] at H
  dsimp'
  simp only [if_congr, Subtype.mk_lt_mk, dif_ctx_congr]
  split_ifs
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with two of them by hand.
  pick_goal 8
  · exact (Nat.succ_pred_eq_of_posₓ (lt_of_le_of_ltₓ (zero_le _) ‹_›)).symm
    
  pick_goal 7
  · have : k ≤ i := Nat.le_of_pred_lt ‹_›
    linarith
    
  -- Hope for the best from `linarith`:
  all_goals
    try
        first |
          rfl|
          simp at * <;>
      linarith

/-- The first part of the third simplicial identity -/
theorem δ_comp_σ_self {n} {i : Finₓ (n + 1)} : δ i.cast_succ ≫ σ i = 𝟙 [n] := by
  ext j
  suffices
    ite (Finₓ.castSucc i < ite (j < i) (Finₓ.castSucc j) j.succ) (ite (j < i) (j : ℕ) (j + 1) - 1)
        (ite (j < i) j (j + 1)) =
      j
    by
    dsimp' [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
    simpa [Finₓ.predAbove] with push_cast
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp'
  simp only [if_congr, Subtype.mk_lt_mk]
  split_ifs <;>
    · simp at * <;> linarith
      

/-- The second part of the third simplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n + 1)} : δ i.succ ≫ σ i = 𝟙 [n] := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp' [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
  simp' [Finₓ.predAbove] with push_cast
  split_ifs <;>
    · simp at * <;> linarith
      

/-- The fourth simplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : j.cast_succ < i) :
    δ i.succ ≫ σ j.cast_succ = σ j ≫ δ i := by
  ext k
  dsimp' [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Subtype.mk_lt_mk, Finₓ.cast_succ_mk] at H
  suffices ite (_ < ite (k < i + 1) _ _) _ _ = ite _ (ite (j < k) (k - 1) k) (ite (j < k) (k - 1) k + 1) by
    simpa [apply_dite Finₓ.castSucc, Finₓ.predAbove] with push_cast
  split_ifs
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with three of them by hand.
  swap
  · simp only [Subtype.mk_lt_mk] at h_1
    simp only [not_ltₓ] at h_2
    simp only [self_eq_add_rightₓ, one_ne_zero]
    exact
      lt_irreflₓ (k - 1)
        (lt_of_lt_of_leₓ (Nat.pred_ltₓ (ne_of_ltₓ (lt_of_le_of_ltₓ (zero_le _) h_1)).symm)
          (le_transₓ (Nat.le_of_lt_succₓ h) h_2))
    
  pick_goal 4
  · simp only [Subtype.mk_lt_mk] at h_1
    simp only [not_ltₓ] at h
    simp only [Nat.add_succ_sub_one, add_zeroₓ]
    exfalso
    exact lt_irreflₓ _ (lt_of_le_of_ltₓ (Nat.le_pred_of_ltₓ (Nat.lt_of_succ_leₓ h)) h_3)
    
  pick_goal 4
  · simp only [Subtype.mk_lt_mk] at h_1
    simp only [not_ltₓ] at h_3
    simp only [Nat.add_succ_sub_one, add_zeroₓ]
    exact (Nat.succ_pred_eq_of_posₓ (lt_of_le_of_ltₓ (zero_le _) h_2)).symm
    
  -- Hope for the best from `linarith`:
  all_goals
    simp at h_1 h_2⊢ <;> linarith

attribute [local simp] Finₓ.pred_mk

/-- The fifth simplicial identity -/
theorem σ_comp_σ {n} {i j : Finₓ (n + 1)} (H : i ≤ j) : σ i.cast_succ ≫ σ j = σ j.succ ≫ σ i := by
  ext k
  dsimp' [σ, Finₓ.predAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Subtype.mk_le_mk] at H
  -- At this point `simp with push_cast` makes good progress, but neither `simp?` nor `squeeze_simp`
  -- return usable sets of lemmas.
  -- To avoid using a non-terminal simp, we make a `suffices` statement indicating the shape
  -- of the goal we're looking for, and then use `simpa with push_cast`.
  -- I'm not sure this is actually much more robust that a non-terminal simp.
  suffices ite (_ < dite (i < k) _ _) _ _ = ite (_ < dite (j + 1 < k) _ _) _ _ by
    simpa [Finₓ.predAbove] with push_cast
  split_ifs
  -- `split_ifs` created 12 goals.
  -- Most of them are dealt with `by simp at *; linarith`,
  -- but we pull out two harder ones to do by hand.
  pick_goal 3
  · simp only [not_ltₓ] at h_2
    exact
      False.elim
        (lt_irreflₓ (k - 1)
          (lt_of_lt_of_leₓ (Nat.pred_ltₓ (id (ne_of_ltₓ (lt_of_le_of_ltₓ (zero_le i) h)).symm))
            (le_transₓ h_2 (Nat.succ_le_of_ltₓ h_1))))
    
  pick_goal 3
  · simp only [Subtype.mk_lt_mk, not_ltₓ] at h_1
    exact False.elim (lt_irreflₓ j (lt_of_lt_of_leₓ (Nat.pred_lt_predₓ (Nat.succ_ne_zero j) h_2) h_1))
    
  -- Deal with the rest automatically.
  all_goals
    simp at * <;> linarith

end Generators

section Skeleton

/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrdₓ.{v} where
  obj := fun a => NonemptyFinLinOrdₓ.of <| ULift (Finₓ (a.len + 1))
  map := fun a b f => ⟨fun i => ULift.up (f.toOrderHom i.down), fun i j h => f.toOrderHom.Monotone h⟩
  map_id' := fun a => by
    ext
    simp
  map_comp' := fun a b c f g => by
    ext
    simp

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Finₓ (X.len + 1)) = Fintype.card (Finₓ (Y.len + 1)) by
    ext
    simpa
  · apply Fintype.card_congr
    refine' equiv.ulift.symm.trans (((skeletal_functor ⋙ forget _).mapIso I).toEquiv.trans _)
    apply Equivₓ.ulift
    

namespace SkeletalFunctor

instance : Full skeletalFunctor.{v} where
  preimage := fun a b f => SimplexCategory.Hom.mk ⟨fun i => (f (ULift.up i)).down, fun i j h => f.Monotone h⟩
  witness' := by
    intro m n f
    dsimp'  at *
    ext1 ⟨i⟩
    ext1
    ext1
    cases x
    simp

instance : Faithful skeletalFunctor.{v} where
  map_injective' := fun m n f g h => by
    ext1
    ext1
    ext1 i
    apply ULift.up.inj
    change (skeletal_functor.map f) ⟨i⟩ = (skeletal_functor.map g) ⟨i⟩
    rw [h]

instance : EssSurj skeletalFunctor.{v} where
  mem_ess_image := fun X =>
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_posₓ <| fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (finset.univ.order_emb_of_fin aux).StrictMono
        refine' { Hom := ⟨fun i => f i.down, _⟩, inv := ⟨fun i => ⟨f.symm i⟩, _⟩, hom_inv_id' := _, inv_hom_id' := _ }
        · rintro ⟨i⟩ ⟨j⟩ h
          show f i ≤ f j
          exact hf.monotone h
          
        · intro i j h
          show f.symm i ≤ f.symm j
          rw [← hf.le_iff_le]
          show f (f.symm i) ≤ f (f.symm j)
          simpa only [OrderIso.apply_symm_apply]
          
        · ext1
          ext1 ⟨i⟩
          ext1
          exact f.symm_apply_apply i
          
        · ext1
          ext1 i
          exact f.apply_symm_apply i
          ⟩⟩

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor.{v} :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor

end SkeletalFunctor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrdₓ.{v} :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

/-- `simplex_category` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def isSkeletonOf : IsSkeletonOf NonemptyFinLinOrdₓ SimplexCategory skeletalFunctor.{v} where
  skel := skeletal
  eqv := skeletalFunctor.isEquivalence

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  { a : SimplexCategory // a.len ≤ n }deriving SmallCategory

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨[0], by
      simp ⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion {n : ℕ} : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _ deriving Full, Faithful

end Truncated

section Concrete

instance : ConcreteCategory.{0} SimplexCategory where
  forget := { obj := fun i => Finₓ (i.len + 1), map := fun i j f => f.toOrderHom }
  forget_faithful := {  }

end Concrete

section EpiMono

/-- A morphism in `simplex_category` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} : Mono f ↔ Function.Injective f.toOrderHom := by
  constructor
  · intro m x y h
    have H : const n x ≫ f = const n y ≫ f := by
      dsimp'
      rw [h]
    change (n.const x).toOrderHom 0 = (n.const y).toOrderHom 0
    rw [cancel_mono f] at H
    rw [H]
    
  · exact concrete_category.mono_of_injective f
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:50: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:59:31: expecting tactic arg
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:50: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:59:31: expecting tactic arg
/-- A morphism in `simplex_category` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} : Epi f ↔ Function.Surjective f.toOrderHom := by
  constructor
  · intro hyp_f_epi x
    by_contra' h_ab
    -- The proof is by contradiction: assume f is not surjective,
    -- then introduce two non-equal auxiliary functions equalizing f, and get a contradiction.
    -- First we define the two auxiliary functions.
    set chi_1 : m ⟶ [1] :=
      hom.mk
        ⟨fun u => if u ≤ x then 0 else 1, by
          intro a b h
          dsimp' only
          split_ifs with h1 h2 h3
          any_goals {
          }
          · exact bot_le
            
          · exact False.elim (h1 (le_transₓ h h3))
            ⟩
    set chi_2 : m ⟶ [1] :=
      hom.mk
        ⟨fun u => if u < x then 0 else 1, by
          intro a b h
          dsimp' only
          split_ifs with h1 h2 h3
          any_goals {
          }
          · exact bot_le
            
          · exact False.elim (h1 (lt_of_le_of_ltₓ h h3))
            ⟩
    -- The two auxiliary functions equalize f
    have f_comp_chi_i : f ≫ chi_1 = f ≫ chi_2 := by
      dsimp'
      ext
      simp [le_iff_lt_or_eqₓ, h_ab x_1]
    -- We now just have to show the two auxiliary functions are not equal.
    rw [CategoryTheory.cancel_epi f] at f_comp_chi_i
    rename' f_comp_chi_i => eq_chi_i
    apply_fun fun e => e.toOrderHom x  at eq_chi_i
    suffices (0 : Finₓ 2) = 1 by
      exact bot_ne_top this
    simpa using eq_chi_i
    
  · exact concrete_category.epi_of_surjective f
    

/-- A monomorphism in `simplex_category` must increase lengths-/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  have f_inj : Function.Injective f.to_order_hom.to_fun := mono_iff_injective.elim_left hyp_f_mono
  simpa using Fintype.card_le_of_injective f.to_order_hom.to_fun f_inj

theorem le_of_mono {n m : ℕ} {f : [n] ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono

/-- An epimorphism in `simplex_category` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.to_order_hom.to_fun := epi_iff_surjective.elim_left hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.to_order_hom.to_fun f_surj

theorem le_of_epi {n m : ℕ} {f : [n] ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi

instance {n : ℕ} {i : Finₓ (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Finₓ.succ_above_right_injective

instance {n : ℕ} {i : Finₓ (n + 1)} : Epi (σ i) := by
  rw [epi_iff_surjective]
  intro b
  simp only [σ, mk_hom, hom.to_order_hom_mk, OrderHom.coe_fun_mk]
  by_cases' b ≤ i
  · use b
    rw
      [Finₓ.pred_above_below i b
        (by
          simpa only [Finₓ.coe_eq_cast_succ] using h)]
    simp only [Finₓ.coe_eq_cast_succ, Finₓ.cast_pred_cast_succ]
    
  · use b.succ
    rw [Finₓ.pred_above_above i b.succ _, Finₓ.pred_succ]
    rw [not_leₓ] at h
    rw [Finₓ.lt_iff_coe_lt_coe] at h⊢
    simpa only [Finₓ.coe_succ, Finₓ.coe_cast_succ] using Nat.Lt.step h
    

instance : ReflectsIsomorphisms (forget SimplexCategory) :=
  ⟨by
    intro x y f
    intro
    exact
      is_iso.of_iso
        { Hom := f,
          inv :=
            hom.mk
              { toFun := inv ((forget SimplexCategory).map f),
                monotone' := fun y₁ y₂ h => by
                  by_cases' h' : y₁ < y₂
                  · by_contra h''
                    have eq := fun i => congr_hom (iso.inv_hom_id (as_iso ((forget _).map f))) i
                    have ineq := f.to_order_hom.monotone' (le_of_not_geₓ h'')
                    dsimp'  at ineq
                    erw [Eq, Eq] at ineq
                    exact not_le.mpr h' ineq
                    
                  · rw [eq_of_le_of_not_lt h h']
                     },
          hom_inv_id' := by
            ext1
            ext1
            exact iso.hom_inv_id (as_iso ((forget _).map f)),
          inv_hom_id' := by
            ext1
            ext1
            exact iso.inv_hom_id (as_iso ((forget _).map f)) }⟩

theorem is_iso_of_bijective {x y : SimplexCategory} {f : x ⟶ y} (hf : Function.Bijective f.toOrderHom.toFun) :
    IsIso f :=
  have : is_iso ((forget SimplexCategory).map f) := (is_iso_iff_bijective _).mpr hf
  is_iso_of_reflects_iso f (forget SimplexCategory)

/-- An isomorphism in `simplex_category` induces an `order_iso`. -/
@[simp]
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Finₓ (x.len + 1) ≃o Finₓ (y.len + 1) :=
  Equivₓ.toOrderIso
    { toFun := e.Hom.toOrderHom, invFun := e.inv.toOrderHom,
      left_inv := fun i => by
        simpa only using congr_argₓ (fun φ => (hom.to_order_hom φ) i) e.hom_inv_id',
      right_inv := fun i => by
        simpa only using congr_argₓ (fun φ => (hom.to_order_hom φ) i) e.inv_hom_id' }
    e.Hom.toOrderHom.Monotone e.inv.toOrderHom.Monotone

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Finₓ (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.order_emb_of_fin_unique' h fun i => Finset.mem_univ ((order_iso_of_iso e) i)
  have eq₂ := Finset.order_emb_of_fin_unique' h fun i => Finset.mem_univ ((order_iso_of_iso (iso.refl x)) i)
  ext1
  ext1
  convert congr_argₓ (fun φ => OrderEmbedding.toOrderHom φ) (eq₁.trans eq₂.symm)
  ext1
  ext1 i
  rfl

theorem eq_id_of_is_iso {x : SimplexCategory} {f : x ⟶ x} (hf : IsIso f) : f = 𝟙 _ :=
  congr_argₓ (fun φ : _ ≅ _ => φ.Hom) (iso_eq_iso_refl (asIso f))

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ') (i : Finₓ (n + 1))
    (hi : θ.toOrderHom i.cast_succ = θ.toOrderHom i.succ) : ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext1
  ext1
  ext1 x
  simp only [hom.to_order_hom_mk, Function.comp_app, OrderHom.comp_coe, hom.comp, small_category_comp, σ, mk_hom,
    OrderHom.coe_fun_mk]
  by_cases' h' : x ≤ i.cast_succ
  · rw [Finₓ.pred_above_below i x h']
    have eq := Finₓ.cast_succ_cast_pred (gt_of_gt_of_geₓ (Finₓ.cast_succ_lt_last i) h')
    erw [Finₓ.succ_above_below i.succ x.cast_pred _]
    swap
    · rwa [Eq, ← Finₓ.le_cast_succ_iff]
      
    rw [Eq]
    
  · simp only [not_leₓ] at h'
    let y :=
      x.pred
        (by
          intro h
          rw [h] at h'
          simpa only [Finₓ.lt_iff_coe_lt_coe, Nat.not_lt_zeroₓ, Finₓ.coe_zero] using h')
    simp only
      [show x = y.succ by
        rw [Finₓ.succ_pred]] at
      h'⊢
    rw [Finₓ.pred_above_above i y.succ h', Finₓ.pred_succ]
    by_cases' h'' : y = i
    · rw [h'']
      convert hi.symm
      erw [Finₓ.succ_above_below i.succ _]
      exact Finₓ.lt_succ
      
    · erw [Finₓ.succ_above_above i.succ _]
      simp only [Finₓ.lt_iff_coe_lt_coe, Finₓ.le_iff_coe_le_coe, Finₓ.coe_succ, Finₓ.coe_cast_succ, Nat.lt_succ_iffₓ,
        Finₓ.ext_iff] at h' h''⊢
      cases' Nat.Le.dest h' with c hc
      cases c
      · exfalso
        rw [add_zeroₓ] at hc
        rw [hc] at h''
        exact h'' rfl
        
      · rw [← hc]
        simp only [add_le_add_iff_left, Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]
        
      
    

theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) : ∃ (i : Finₓ (n + 1))(θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Finₓ (n + 2), (hom.to_order_hom θ) x = (hom.to_order_hom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases' x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
      
    · refine' ⟨y, x, ⟨h₁.symm, _⟩⟩
      cases' lt_or_eq_of_leₓ (not_lt.mp h) with h' h'
      · exact h'
        
      · exfalso
        exact h₂ h'.symm
        
      
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  let z := x.cast_pred
  use z
  simp only [← show z.cast_succ = x from Finₓ.cast_succ_cast_pred (lt_of_lt_of_leₓ h₂ (Finₓ.le_last y))] at h₁ h₂
  apply eq_σ_comp_of_not_injective'
  rw [Finₓ.cast_succ_lt_iff_succ_le] at h₂
  apply le_antisymmₓ
  · exact θ.to_order_hom.monotone (le_of_ltₓ (Finₓ.cast_succ_lt_succ z))
    
  · rw [h₁]
    exact θ.to_order_hom.monotone h₂
    

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1)) (i : Finₓ (n + 2))
    (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i := by
  by_cases' i < Finₓ.last (n + 1)
  · use θ ≫ σ (Finₓ.castPred i)
    ext1
    ext1
    ext1 x
    simp only [hom.to_order_hom_mk, Function.comp_app, OrderHom.comp_coe, hom.comp, small_category_comp]
    by_cases' h' : θ.to_order_hom x ≤ i
    · simp only [σ, mk_hom, hom.to_order_hom_mk, OrderHom.coe_fun_mk]
      erw
        [Finₓ.pred_above_below (Finₓ.castPred i) (θ.to_order_hom x)
          (by
            simpa [Finₓ.cast_succ_cast_pred h] using h')]
      erw [Finₓ.succ_above_below i]
      swap
      · simp only [Finₓ.lt_iff_coe_lt_coe, Finₓ.coe_cast_succ]
        exact lt_of_le_of_ltₓ (Finₓ.coe_cast_pred_le_self _) (fin.lt_iff_coe_lt_coe.mp ((Ne.le_iff_lt (hi x)).mp h'))
        
      rw [Finₓ.cast_succ_cast_pred]
      apply lt_of_le_of_ltₓ h' h
      
    · simp only [not_leₓ] at h'
      simp only [σ, mk_hom, hom.to_order_hom_mk, OrderHom.coe_fun_mk,
        Finₓ.pred_above_above (Finₓ.castPred i) (θ.to_order_hom x)
          (by
            simpa only [Finₓ.cast_succ_cast_pred h] using h')]
      erw [Finₓ.succ_above_above i _, Finₓ.succ_pred]
      simpa only [Finₓ.le_iff_coe_le_coe, Finₓ.coe_cast_succ, Finₓ.coe_pred] using
        Nat.le_pred_of_ltₓ (fin.lt_iff_coe_lt_coe.mp h')
      
    
  · obtain rfl := le_antisymmₓ (Finₓ.le_last i) (not_lt.mp h)
    use θ ≫ σ (Finₓ.last _)
    ext1
    ext1
    ext1 x
    simp only [hom.to_order_hom_mk, Function.comp_app, OrderHom.comp_coe, hom.comp, small_category_comp, σ, δ, mk_hom,
      OrderHom.coe_fun_mk, OrderEmbedding.to_order_hom_coe, Finₓ.pred_above_last, Finₓ.succ_above_last,
      Finₓ.cast_succ_cast_pred ((Ne.le_iff_lt (hi x)).mp (Finₓ.le_last _))]
    

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) : ∃ (i : Finₓ (n + 2))(θ' : Δ ⟶ mk n), θ = θ' ≫ δ i := by
  cases' not_forall.mp hθ with i hi
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ := by
  apply eq_id_of_is_iso
  apply is_iso_of_bijective
  erw [Fintype.bijective_iff_injective_and_card i.to_order_hom, ← mono_iff_injective, eq_self_iff_true, and_trueₓ]
  infer_instance

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ := by
  apply eq_id_of_is_iso
  apply is_iso_of_bijective
  erw [Fintype.bijective_iff_surjective_and_card i.to_order_hom, ← epi_iff_surjective, eq_self_iff_true, and_trueₓ]
  infer_instance

theorem eq_σ_of_epi {n : ℕ} (θ : mk (n + 1) ⟶ mk n) [Epi θ] : ∃ i : Finₓ (n + 1), θ = σ i := by
  rcases eq_σ_comp_of_not_injective θ _ with ⟨i, θ', h⟩
  swap
  · by_contra
    simpa only [Nat.one_ne_zero, add_le_iff_nonpos_right, nonpos_iff_eq_zero] using
      le_of_mono (mono_iff_injective.mpr h)
    
  use i
  have : epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  have := CategoryTheory.epi_of_epi (σ i) θ'
  erw [h, eq_id_of_epi θ', category.comp_id]

theorem eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n + 1)) [Mono θ] : ∃ i : Finₓ (n + 2), θ = δ i := by
  rcases eq_comp_δ_of_not_surjective θ _ with ⟨i, θ', h⟩
  swap
  · by_contra
    simpa only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] using le_of_epi (epi_iff_surjective.mpr h)
    
  use i
  have : mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  have := CategoryTheory.mono_of_mono θ' (δ i)
  erw [h, eq_id_of_mono θ', category.id_comp]

end EpiMono

end SimplexCategory

