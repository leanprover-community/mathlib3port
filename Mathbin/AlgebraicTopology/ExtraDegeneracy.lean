/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.SimplicialSet
import Mathbin.AlgebraicTopology.CechNerve
import Mathbin.Tactic.FinCases

/-!

# Augmented simplicial objects with an extra degeneracy

In simplicial homotopy theory, in order to prove that the connected components
of a simplicial set `X` are contractible, it suffices to construct an extra
degeneracy as it is defined in *Simplicial Homotopy Theory* by Goerss-Jardine p. 190.
It consists of a series of maps `π₀ X → X _[0]` and `X _[n] → X _[n+1]` which
behave formally like an extra degeneracy `σ (-1)`. It can be thought as a datum
associated to the augmented simplicial set `X → π₀ X`.

In this file, we adapt this definition to the case of augmented
simplicial objects in any category.

## Main definitions

- the structure `extra_degeneracy X` for any `X : simplicial_object.augmented C`
- `extra_degeneracy.map`: extra degeneracies are preserved by the application of any
functor `C ⥤ D`
- `sSet.augmented.standard_simplex.extra_degeneracy`: the standard `n`-simplex has
an extra degeneracy
- `arrow.augmented_cech_nerve.extra_degeneracy`: the Čech nerve of a split
epimorphism has an extra degeneracy

TODO @joelriou:
1) when the category `C` is preadditive and has a zero object, and
`X : simplicial_object.augmented C` has an extra degeneracy, then the augmentation
on the alternating face map complex of `X` is a homotopy equivalence of chain
complexes.

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/


open CategoryTheory CategoryTheory.Category

open CategoryTheory.SimplicialObject.Augmented

open Opposite

open Simplicial

namespace SimplicialObject

namespace Augmented

variable {C : Type _} [Category C]

/-- The datum of an extra degeneracy is a technical condition on
augmented simplicial objects. The morphisms `s'` and `s n` of the
structure formally behave like extra degeneracies `σ (-1)`. -/
@[ext]
structure ExtraDegeneracy (X : SimplicialObject.Augmented C) where
  s' : point.obj X ⟶ drop.obj X _[0]
  s : ∀ n : ℕ, drop.obj X _[n] ⟶ drop.obj X _[n + 1]
  s'_comp_ε' : s' ≫ X.Hom.app (op [0]) = 𝟙 _
  s₀_comp_δ₁' : s 0 ≫ (drop.obj X).δ 1 = X.Hom.app (op [0]) ≫ s'
  s_comp_δ₀' : ∀ n : ℕ, s n ≫ (drop.obj X).δ 0 = 𝟙 _
  s_comp_δ' : ∀ (n : ℕ) (i : Finₓ (n + 2)), s (n + 1) ≫ (drop.obj X).δ i.succ = (drop.obj X).δ i ≫ s n
  s_comp_σ' : ∀ (n : ℕ) (i : Finₓ (n + 1)), s n ≫ (drop.obj X).σ i.succ = (drop.obj X).σ i ≫ s (n + 1)

namespace ExtraDegeneracy

restate_axiom s'_comp_ε'

restate_axiom s₀_comp_δ₁'

restate_axiom s_comp_δ₀'

restate_axiom s_comp_δ'

restate_axiom s_comp_σ'

attribute [reassoc] s'_comp_ε s₀_comp_δ₁ s_comp_δ₀ s_comp_δ s_comp_σ

attribute [simp] s'_comp_ε s_comp_δ₀

/-- If `ed` is an extra degeneracy for `X : simplicial_object.augmented C` and
`F : C ⥤ D` is a functor, then `ed.map F` is an extra degeneracy for the
augmented simplical object in `D` obtained by applying `F` to `X`. -/
def map {D : Type _} [Category D] {X : SimplicialObject.Augmented C} (ed : ExtraDegeneracy X) (F : C ⥤ D) :
    ExtraDegeneracy (((whiskering _ _).obj F).obj X) where
  s' := F.map ed.s'
  s := fun n => F.map (ed.s n)
  s'_comp_ε' := by
    dsimp
    erw [comp_id, ← F.map_comp, ed.s'_comp_ε, F.map_id]
  s₀_comp_δ₁' := by
    dsimp
    erw [comp_id, ← F.map_comp, ← F.map_comp, ed.s₀_comp_δ₁]
  s_comp_δ₀' := fun n => by
    dsimp
    erw [← F.map_comp, ed.s_comp_δ₀, F.map_id]
  s_comp_δ' := fun n i => by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
    rfl
  s_comp_σ' := fun n i => by
    dsimp
    erw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]
    rfl

/-- If `X` and `Y` are isomorphic augmented simplicial objects, then an extra
degeneracy for `X` gives also an extra degeneracy for `Y` -/
def ofIso {X Y : SimplicialObject.Augmented C} (e : X ≅ Y) (ed : ExtraDegeneracy X) : ExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).Hom.app (op [0])
  s := fun n => (drop.mapIso e).inv.app (op [n]) ≫ ed.s n ≫ (drop.mapIso e).Hom.app (op [n + 1])
  s'_comp_ε' := by simpa only [functor.map_iso, assoc, w₀, ed.s'_comp_ε_assoc] using (point.map_iso e).inv_hom_id
  s₀_comp_δ₁' := by
    have h := w₀ e.inv
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.δ_naturality, ed.s₀_comp_δ₁_assoc, reassoc_of h]
  s_comp_δ₀' := fun n => by
    have h := ed.s_comp_δ₀'
    dsimp at h⊢
    simpa only [assoc, ← simplicial_object.δ_naturality, reassoc_of h] using
      congr_app (drop.map_iso e).inv_hom_id (op [n])
  s_comp_δ' := fun n i => by
    have h := ed.s_comp_δ' n i
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.δ_naturality, reassoc_of h, ← simplicial_object.δ_naturality_assoc]
  s_comp_σ' := fun n i => by
    have h := ed.s_comp_σ' n i
    dsimp at h⊢
    simp only [assoc, ← simplicial_object.σ_naturality, reassoc_of h, ← simplicial_object.σ_naturality_assoc]

end ExtraDegeneracy

end Augmented

end SimplicialObject

namespace SSet

namespace Augmented

namespace StandardSimplex

/-- When `[has_zero X]`, the shift of a map `f : fin n → X`
is a map `fin (n+1) → X` which sends `0` to `0` and `i.succ` to `f i`. -/
def shiftFun {n : ℕ} {X : Type _} [Zero X] (f : Finₓ n → X) (i : Finₓ (n + 1)) : X :=
  dite (i = 0) (fun h => 0) fun h => f (i.pred h)

@[simp]
theorem shift_fun_0 {n : ℕ} {X : Type _} [Zero X] (f : Finₓ n → X) : shiftFun f 0 = 0 :=
  rfl

@[simp]
theorem shift_fun_succ {n : ℕ} {X : Type _} [Zero X] (f : Finₓ n → X) (i : Finₓ n) : shiftFun f i.succ = f i := by
  dsimp [shift_fun]
  split_ifs
  · exfalso
    simpa only [Finₓ.ext_iff, Finₓ.coe_succ] using h
    
  · simp only [Finₓ.pred_succ]
    

/-- The shift of a morphism `f : [n] → Δ` in `simplex_category` corresponds to
the monotone map which sends `0` to `0` and `i.succ` to `f.to_order_hom i`. -/
@[simp]
def shift {n : ℕ} {Δ : SimplexCategory} (f : [n] ⟶ Δ) : [n + 1] ⟶ Δ :=
  SimplexCategory.Hom.mk
    { toFun := shiftFun f.toOrderHom,
      monotone' := fun i₁ i₂ hi => by
        by_cases h₁:i₁ = 0
        · subst h₁
          simp only [shift_fun_0, Finₓ.zero_le]
          
        · have h₂ : i₂ ≠ 0 := by
            intro h₂
            subst h₂
            exact h₁ (le_antisymmₓ hi (Finₓ.zero_le _))
          cases' Finₓ.eq_succ_of_ne_zero h₁ with j₁ hj₁
          cases' Finₓ.eq_succ_of_ne_zero h₂ with j₂ hj₂
          substs hj₁ hj₂
          simpa only [shift_fun_succ] using f.to_order_hom.monotone (fin.succ_le_succ_iff.mp hi)
           }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The obvious extra degeneracy on the standard simplex. -/
@[protected]
def extraDegeneracy (Δ : SimplexCategory) : SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ) where
  s' := fun x => SimplexCategory.Hom.mk (OrderHom.const _ 0)
  s := fun n f => shift f
  s'_comp_ε' := by
    ext1 j
    fin_cases j
  s₀_comp_δ₁' := by
    ext x j
    fin_cases j
    rfl
  s_comp_δ₀' := fun n => by
    ext φ i : 4
    dsimp [simplicial_object.δ, SimplexCategory.δ, SSet.standardSimplex]
    simp only [shift_fun_succ]
  s_comp_δ' := fun n i => by
    ext φ j : 4
    dsimp [simplicial_object.δ, SimplexCategory.δ, SSet.standardSimplex]
    by_cases j = 0
    · subst h
      simp only [Finₓ.succ_succ_above_zero, shift_fun_0]
      
    · cases' Finₓ.eq_succ_of_ne_zero h with k hk
      subst hk
      simp only [Finₓ.succ_succ_above_succ, shift_fun_succ]
      
  s_comp_σ' := fun n i => by
    ext φ j : 4
    dsimp [simplicial_object.σ, SimplexCategory.σ, SSet.standardSimplex]
    by_cases j = 0
    · subst h
      simpa only [shift_fun_0] using shift_fun_0 φ.to_order_hom
      
    · cases' Finₓ.eq_succ_of_ne_zero h with k hk
      subst hk
      simp only [Finₓ.succ_pred_above_succ, shift_fun_succ]
      

instance nonempty_extra_degeneracy_standard_simplex (Δ : SimplexCategory) :
    Nonempty (SimplicialObject.Augmented.ExtraDegeneracy (standardSimplex.obj Δ)) :=
  ⟨standardSimplex.extraDegeneracy Δ⟩

end StandardSimplex

end Augmented

end SSet

namespace CategoryTheory

open Limits

namespace Arrow

namespace AugmentedCechNerve

variable {C : Type _} [Category C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun i : Finₓ (n + 1) => f.left) fun i => f.Hom] (S : SplitEpi f.Hom)

include S

/-- The extra degeneracy map on the Čech nerve of a split epi. It is
given on the `0`-projection by the given section of the split epi,
and by shifting the indices on the other projections. -/
noncomputable def ExtraDegeneracy.s (n : ℕ) : f.cechNerve.obj (op [n]) ⟶ f.cechNerve.obj (op [n + 1]) :=
  widePullback.lift (widePullback.base _)
    (fun i => dite (i = 0) (fun h => widePullback.base _ ≫ S.section_) fun h => widePullback.π _ (i.pred h)) fun i => by
    split_ifs
    · subst h
      simp only [assoc, split_epi.id, comp_id]
      
    · simp only [wide_pullback.π_arrow]
      

@[simp]
theorem ExtraDegeneracy.s_comp_π_0 (n : ℕ) :
    ExtraDegeneracy.s f S n ≫ widePullback.π _ 0 = widePullback.base _ ≫ S.section_ := by
  dsimp [extra_degeneracy.s]
  simpa only [wide_pullback.lift_π]

@[simp]
theorem ExtraDegeneracy.s_comp_π_succ (n : ℕ) (i : Finₓ (n + 1)) :
    ExtraDegeneracy.s f S n ≫ widePullback.π _ i.succ = widePullback.π _ i := by
  dsimp [extra_degeneracy.s]
  simp only [wide_pullback.lift_π]
  split_ifs
  · exfalso
    simpa only [Finₓ.ext_iff, Finₓ.coe_succ, Finₓ.coe_zero, Nat.succ_ne_zero] using h
    
  · congr
    apply Finₓ.pred_succ
    

@[simp]
theorem ExtraDegeneracy.s_comp_base (n : ℕ) : ExtraDegeneracy.s f S n ≫ widePullback.base _ = widePullback.base _ := by
  apply wide_pullback.lift_base

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The augmented Čech nerve associated to a split epimorphism has an extra degeneracy. -/
noncomputable def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy f.augmentedCechNerve where
  s' := S.section_ ≫ widePullback.lift f.Hom (fun i => 𝟙 _) fun i => by rw [id_comp]
  s := fun n => ExtraDegeneracy.s f S n
  s'_comp_ε' := by simp only [augmented_cech_nerve_hom_app, assoc, wide_pullback.lift_base, split_epi.id]
  s₀_comp_δ₁' := by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · fin_cases j
      simpa only [assoc, wide_pullback.lift_π, comp_id] using extra_degeneracy.s_comp_π_0 f S 0
      
    · simpa only [assoc, wide_pullback.lift_base, split_epi.id, comp_id] using extra_degeneracy.s_comp_base f S 0
      
  s_comp_δ₀' := fun n => by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · simpa only [assoc, wide_pullback.lift_π, id_comp] using extra_degeneracy.s_comp_π_succ f S n j
      
    · simpa only [assoc, wide_pullback.lift_base, id_comp] using extra_degeneracy.s_comp_base f S n
      
  s_comp_δ' := fun n i => by
    dsimp [cech_nerve, simplicial_object.δ, SimplexCategory.δ]
    ext j
    · simp only [assoc, wide_pullback.lift_π]
      by_cases j = 0
      · subst h
        erw [Finₓ.succ_succ_above_zero, extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0]
        dsimp
        simp only [wide_pullback.lift_base_assoc]
        
      · cases' Finₓ.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Finₓ.succ_succ_above_succ, extra_degeneracy.s_comp_π_succ, extra_degeneracy.s_comp_π_succ]
        dsimp
        simp only [wide_pullback.lift_π]
        
      
    · simp only [assoc, wide_pullback.lift_base]
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base]
      dsimp
      simp only [wide_pullback.lift_base]
      
  s_comp_σ' := fun n i => by
    dsimp [cech_nerve, simplicial_object.σ, SimplexCategory.σ]
    ext j
    · simp only [assoc, wide_pullback.lift_π]
      by_cases j = 0
      · subst h
        erw [extra_degeneracy.s_comp_π_0, extra_degeneracy.s_comp_π_0]
        dsimp
        simp only [wide_pullback.lift_base_assoc]
        
      · cases' Finₓ.eq_succ_of_ne_zero h with k hk
        subst hk
        erw [Finₓ.succ_pred_above_succ, extra_degeneracy.s_comp_π_succ, extra_degeneracy.s_comp_π_succ]
        dsimp
        simp only [wide_pullback.lift_π]
        
      
    · simp only [assoc, wide_pullback.lift_base]
      erw [extra_degeneracy.s_comp_base, extra_degeneracy.s_comp_base]
      dsimp
      simp only [wide_pullback.lift_base]
      

end AugmentedCechNerve

end Arrow

end CategoryTheory

