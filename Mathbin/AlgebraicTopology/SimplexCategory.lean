/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathbin.CategoryTheory.Skeletal
import Mathbin.Tactic.Linarith.Default
import Mathbin.Data.Fintype.Sort
import Mathbin.Order.Category.NonemptyFinLinOrd

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


universe u v

open CategoryTheory

-- ././Mathport/Syntax/Translate/Basic.lean:1202:31: unsupported: @[derive, irreducible] def
/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `fin (n+1) → fin (m+1)`
-/
irreducible_def SimplexCategory :=
  ULift.{u} ℕ

namespace SimplexCategory

section

attribute [local semireducible] SimplexCategory

/-- Interpet a natural number as an object of the simplex category. -/
-- TODO: Make `mk` irreducible.
def mk (n : ℕ) : SimplexCategory.{u} :=
  ULift.up n

-- mathport name: «expr[ ]»
localized [Simplicial] notation "[" n "]" => SimplexCategory.mk n

/-- The length of an object of `simplex_category`. -/
-- TODO: Make `len` irreducible.
def len (n : SimplexCategory.{u}) : ℕ :=
  n.down

@[ext]
theorem ext (a b : SimplexCategory.{u}) : a.len = b.len → a = b :=
  ULift.ext a b

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl

@[simp]
theorem mk_len (n : SimplexCategory.{u}) : [n.len] = n := by
  cases n
  rfl

/-- Morphisms in the simplex_category. -/
@[nolint has_inhabited_instance]
protected irreducible_def Hom (a b : SimplexCategory.{u}) : Type u :=
  ULift (Finₓ (a.len + 1) →o Finₓ (b.len + 1))

namespace Hom

attribute [local semireducible] SimplexCategory.Hom

/-- Make a moprhism in `simplex_category` from a monotone map of fin's. -/
def mk {a b : SimplexCategory.{u}} (f : Finₓ (a.len + 1) →o Finₓ (b.len + 1)) : SimplexCategory.Hom a b :=
  ULift.up f

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory.{u}} (f : SimplexCategory.Hom a b) : Finₓ (a.len + 1) →o Finₓ (b.len + 1) :=
  ULift.down f

@[ext]
theorem ext {a b : SimplexCategory.{u}} (f g : SimplexCategory.Hom a b) : f.toOrderHom = g.toOrderHom → f = g :=
  ULift.ext _ _

@[simp]
theorem mk_to_order_hom {a b : SimplexCategory.{u}} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f := by
  cases f
  rfl

@[simp]
theorem to_order_hom_mk {a b : SimplexCategory.{u}} (f : Finₓ (a.len + 1) →o Finₓ (b.len + 1)) :
    (mk f).toOrderHom = f := by
  simp [to_order_hom, mk]

theorem mk_to_order_hom_apply {a b : SimplexCategory.{u}} (f : Finₓ (a.len + 1) →o Finₓ (b.len + 1))
    (i : Finₓ (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `simplex_category`. -/
@[simp]
def id (a : SimplexCategory.{u}) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `simplex_category`. -/
@[simp]
def comp {a b c : SimplexCategory.{u}} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

@[simps]
instance smallCategory : SmallCategory.{u} SimplexCategory where
  Hom := fun n m => SimplexCategory.Hom n m
  id := fun m => SimplexCategory.Hom.id _
  comp := fun _ _ _ f g => SimplexCategory.Hom.comp g f

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory.{u}) (i : Finₓ (x.len + 1)) : [0] ⟶ x :=
  hom.mk <|
    ⟨fun _ => i, by
      tauto⟩

@[simp]
theorem const_comp (x y : SimplexCategory.{u}) (i : Finₓ (x.len + 1)) (f : x ⟶ y) :
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
  dsimp
  apply Subsingleton.elimₓ

end

open_locale Simplicial

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
  dsimp [δ, Finₓ.succAbove]
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
    dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
    simpa [Finₓ.predAbove] with push_cast
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  simp only [Subtype.mk_le_mk, Finₓ.cast_succ_mk] at H
  dsimp
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
    dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
    simpa [Finₓ.predAbove] with push_cast
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp
  simp only [if_congr, Subtype.mk_lt_mk]
  split_ifs <;>
    · simp at * <;> linarith
      

/-- The second part of the third simplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n + 1)} : δ i.succ ≫ σ i = 𝟙 [n] := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
  simp' [Finₓ.predAbove] with push_cast
  split_ifs <;>
    · simp at * <;> linarith
      

/-- The fourth simplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : j.cast_succ < i) :
    δ i.succ ≫ σ j.cast_succ = σ j ≫ δ i := by
  ext k
  dsimp [δ, σ, Finₓ.succAbove, Finₓ.predAbove]
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
    exact lt_irreflₓ _ (lt_of_le_of_ltₓ (Nat.le_pred_of_lt (Nat.lt_of_succ_leₓ h)) h_3)
    
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
  dsimp [σ, Finₓ.predAbove]
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
def skeletalFunctor : SimplexCategory.{u} ⥤ NonemptyFinLinOrdₓ.{v} where
  obj := fun a => NonemptyFinLinOrdₓ.of <| ULift (Finₓ (a.len + 1))
  map := fun a b f => ⟨fun i => ULift.up (f.toOrderHom i.down), fun i j h => f.toOrderHom.Monotone h⟩
  map_id' := fun a => by
    ext
    simp
  map_comp' := fun a b c f g => by
    ext
    simp

theorem skeletal : Skeletal SimplexCategory.{u} := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Finₓ (X.len + 1)) = Fintype.card (Finₓ (Y.len + 1)) by
    ext
    simpa
  · apply Fintype.card_congr
    refine' equiv.ulift.symm.trans (((skeletal_functor ⋙ forget _).mapIso I).toEquiv.trans _)
    apply Equivₓ.ulift
    

namespace SkeletalFunctor

instance : Full skeletalFunctor.{u, v} where
  Preimage := fun a b f => SimplexCategory.Hom.mk ⟨fun i => (f (ULift.up i)).down, fun i j h => f.Monotone h⟩
  witness' := by
    intro m n f
    dsimp  at *
    ext1 ⟨i⟩
    ext1
    ext1
    cases x
    simp

instance : Faithful skeletalFunctor.{u, v} where
  map_injective' := fun m n f g h => by
    ext1
    ext1
    ext1 i
    apply ULift.up.inj
    change (skeletal_functor.map f) ⟨i⟩ = (skeletal_functor.map g) ⟨i⟩
    rw [h]

instance : EssSurj skeletalFunctor.{u, v} where
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

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor.{u, v} :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor

end SkeletalFunctor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory.{u} ≌ NonemptyFinLinOrdₓ.{v} :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

/-- `simplex_category` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def isSkeletonOf : IsSkeletonOf NonemptyFinLinOrdₓ SimplexCategory skeletalFunctor.{u, v} where
  skel := skeletal
  eqv := skeletalFunctor.isEquivalence

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  { a : SimplexCategory.{u} // a.len ≤ n }deriving SmallCategory

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨[0], by
      simp ⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion {n : ℕ} : SimplexCategory.Truncated.{u} n ⥤ SimplexCategory.{u} :=
  fullSubcategoryInclusion _ deriving Full, Faithful

end Truncated

section Concrete

instance : ConcreteCategory.{0} SimplexCategory.{u} where
  forget := { obj := fun i => Finₓ (i.len + 1), map := fun i j f => f.toOrderHom }
  forget_faithful := {  }

end Concrete

section EpiMono

/-- A morphism in `simplex_category` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory.{u}} {f : n ⟶ m} : Mono f ↔ Function.Injective f.toOrderHom := by
  constructor
  · intros m x y h
    have H : const n x ≫ f = const n y ≫ f := by
      dsimp
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
theorem epi_iff_surjective {n m : SimplexCategory.{u}} {f : n ⟶ m} : Epi f ↔ Function.Surjective f.toOrderHom := by
  constructor
  · intros hyp_f_epi x
    by_contra' h_ab
    -- The proof is by contradiction: assume f is not surjective,
    -- then introduce two non-equal auxiliary functions equalizing f, and get a contradiction.
    -- First we define the two auxiliary functions.
    set chi_1 : m ⟶ [1] :=
      hom.mk
        ⟨fun u => if u ≤ x then 0 else 1, by
          intro a b h
          dsimp only
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
          dsimp only
          split_ifs with h1 h2 h3
          any_goals {
          }
          · exact bot_le
            
          · exact False.elim (h1 (lt_of_le_of_ltₓ h h3))
            ⟩
    -- The two auxiliary functions equalize f
    have f_comp_chi_i : f ≫ chi_1 = f ≫ chi_2 := by
      dsimp
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
theorem len_le_of_mono {x y : SimplexCategory.{u}} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  have f_inj : Function.Injective f.to_order_hom.to_fun := mono_iff_injective.elim_left hyp_f_mono
  simpa using Fintype.card_le_of_injective f.to_order_hom.to_fun f_inj

theorem le_of_mono {n m : ℕ} {f : [n] ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono

/-- An epimorphism in `simplex_category` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory.{u}} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.to_order_hom.to_fun := epi_iff_surjective.elim_left hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.to_order_hom.to_fun f_surj

theorem le_of_epi {n m : ℕ} {f : [n] ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi

end EpiMono

end SimplexCategory

