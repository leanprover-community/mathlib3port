/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.sites.pretopology
! leanprover-community/mathlib commit 9e7c80f638149bfb3504ba8ff48dfdbfc949fb1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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

* [nLab, *Grothendieck pretopology*](https://ncatlab.org/nlab/show/Grothendieck+pretopology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [Stacks, *00VG*](https://stacks.math.columbia.edu/tag/00VG)
-/


universe v u

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Presieve

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

variable (C)

#print CategoryTheory.Pretopology /-
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
structure Pretopology where
  coverings : ∀ X : C, Set (Presieve X)
  has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [IsIso f], Presieve.singleton f ∈ coverings X
  pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) (S), S ∈ coverings X → pullbackArrows f S ∈ coverings Y
  Transitive :
    ∀ ⦃X : C⦄ (S : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), S f → Presieve Y),
      S ∈ coverings X → (∀ ⦃Y⦄ (f) (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X
#align category_theory.pretopology CategoryTheory.Pretopology
-/

namespace Pretopology

instance : CoeFun (Pretopology C) fun _ => ∀ X : C, Set (Presieve X) :=
  ⟨coverings⟩

variable {C}

instance : LE (Pretopology C) where le K₁ K₂ := (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂

#print CategoryTheory.Pretopology.le_def /-
theorem le_def {K₁ K₂ : Pretopology C} : K₁ ≤ K₂ ↔ (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂ :=
  Iff.rfl
#align category_theory.pretopology.le_def CategoryTheory.Pretopology.le_def
-/

variable (C)

instance : PartialOrder (Pretopology C) :=
  { Pretopology.hasLe with
    le_refl := fun K => le_def.mpr le_rfl
    le_trans := fun K₁ K₂ K₃ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun K₁ K₂ h₁₂ h₂₁ => Pretopology.ext _ _ (le_antisymm h₁₂ h₂₁) }

instance : OrderTop (Pretopology C)
    where
  top :=
    { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      Transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top K X S hS := Set.mem_univ _

instance : Inhabited (Pretopology C) :=
  ⟨⊤⟩

#print CategoryTheory.Pretopology.toGrothendieck /-
/-- A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See <https://stacks.math.columbia.edu/tag/00ZC>, or [MM92] Chapter III, Section 2, Equation (2).
-/
def toGrothendieck (K : Pretopology C) : GrothendieckTopology C
    where
  sieves X S := ∃ R ∈ K X, R ≤ (S : Presieve _)
  top_mem' X := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    refine' ⟨_, K.pullbacks g _ hR, _⟩
    rw [← sieve.sets_iff_generate, sieve.pullback_arrows_comm]
    apply sieve.pullback_monotone
    rwa [sieve.gi_generate.gc]
  transitive' := by
    rintro X S ⟨R', hR', RS⟩ R t
    choose t₁ t₂ t₃ using t
    refine' ⟨_, K.transitive _ _ hR' fun _ f hf => t₂ (RS _ hf), _⟩
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
    apply t₃ (RS _ hg) _ hf
#align category_theory.pretopology.to_grothendieck CategoryTheory.Pretopology.toGrothendieck
-/

/- warning: category_theory.pretopology.mem_to_grothendieck -> CategoryTheory.Pretopology.mem_toGrothendieck is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1] (K : CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (X : C) (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Iff (Membership.Mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.hasMem.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ (max u2 u1))} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (fun (_x : CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) => forall (X : C), Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (CategoryTheory.GrothendieckTopology.hasCoeToFun.{u1, u2} C _inst_1) (CategoryTheory.Pretopology.toGrothendieck.{u1, u2} C _inst_1 _inst_2 K) X)) (Exists.{succ (max u2 u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (fun (R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) => Exists.{0} (Membership.Mem.{max u2 u1, max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) (Set.hasMem.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ (max u2 u1))} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (fun (_x : CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) => forall (X : C), Set.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) (CategoryTheory.Pretopology.hasCoeToFun.{u1, u2} C _inst_1 _inst_2) K X)) (fun (H : Membership.Mem.{max u2 u1, max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) (Set.hasMem.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ (max u2 u1))} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (fun (_x : CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) => forall (X : C), Set.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) (CategoryTheory.Pretopology.hasCoeToFun.{u1, u2} C _inst_1 _inst_2) K X)) => LE.le.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Presieve.completeLattice.{u2, u1} C _inst_1 X))))) R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Sieve.{u1, u2} C _inst_1 X) => CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.Sieve.hasCoeToFun.{u1, u2} C _inst_1 X) S))))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1] (K : CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (X : C) (S : CategoryTheory.Sieve.{u1, u2} C _inst_1 X), Iff (Membership.mem.{max u2 u1, max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) (Set.instMembershipSet.{max u2 u1} (CategoryTheory.Sieve.{u1, u2} C _inst_1 X)) S (CategoryTheory.GrothendieckTopology.sieves.{u1, u2} C _inst_1 (CategoryTheory.Pretopology.toGrothendieck.{u1, u2} C _inst_1 _inst_2 K) X)) (Exists.{succ (max u2 u1)} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (fun (R : CategoryTheory.Presieve.{u1, u2} C _inst_1 X) => And (Membership.mem.{max u2 u1, max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Set.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) (Set.instMembershipSet.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X)) R (CategoryTheory.Pretopology.coverings.{u1, u2} C _inst_1 _inst_2 K X)) (LE.le.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (Preorder.toLE.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (CategoryTheory.Presieve.{u1, u2} C _inst_1 X) (CategoryTheory.instCompleteLatticePresieve.{u1, u2} C _inst_1 X))))) R (CategoryTheory.Sieve.arrows.{u1, u2} C _inst_1 X S))))
Case conversion may be inaccurate. Consider using '#align category_theory.pretopology.mem_to_grothendieck CategoryTheory.Pretopology.mem_toGrothendieckₓ'. -/
theorem mem_toGrothendieck (K : Pretopology C) (X S) :
    S ∈ toGrothendieck C K X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X) :=
  Iff.rfl
#align category_theory.pretopology.mem_to_grothendieck CategoryTheory.Pretopology.mem_toGrothendieck

#print CategoryTheory.Pretopology.ofGrothendieck /-
/-- The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def ofGrothendieck (J : GrothendieckTopology C) : Pretopology C
    where
  coverings X R := Sieve.generate R ∈ J X
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by
    rw [Set.mem_def, sieve.pullback_arrows_comm]
    apply J.pullback_stable f hR
  Transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [sieve.pullback_comp]
    apply J.pullback_stable g
    apply J.superset_covering _ (hTi _ hf)
    rintro Y g ⟨W, h, g, hg, rfl⟩
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩
#align category_theory.pretopology.of_grothendieck CategoryTheory.Pretopology.ofGrothendieck
-/

/- warning: category_theory.pretopology.gi -> CategoryTheory.Pretopology.gi is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1], GaloisInsertion.{max u2 u1, max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.partialOrder.{u1, u2} C _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CategoryTheory.GrothendieckTopology.partialOrder.{u1, u2} C _inst_1)) (CategoryTheory.Pretopology.toGrothendieck.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.ofGrothendieck.{u1, u2} C _inst_1 _inst_2)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1], GaloisInsertion.{max u2 u1, max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.instPartialOrderPretopology.{u1, u2} C _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CategoryTheory.GrothendieckTopology.instPartialOrderGrothendieckTopology.{u1, u2} C _inst_1)) (CategoryTheory.Pretopology.toGrothendieck.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.ofGrothendieck.{u1, u2} C _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.pretopology.gi CategoryTheory.Pretopology.giₓ'. -/
/-- We have a galois insertion from pretopologies to Grothendieck topologies. -/
def gi : GaloisInsertion (toGrothendieck C) (ofGrothendieck C)
    where
  gc K J := by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [sieve.gi_generate.gc]
  le_l_u J X S hS := ⟨S, J.superset_covering S.le_generate hS, le_rfl⟩
  choice x hx := toGrothendieck C x
  choice_eq _ _ := rfl
#align category_theory.pretopology.gi CategoryTheory.Pretopology.gi

#print CategoryTheory.Pretopology.trivial /-
/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See <https://stacks.math.columbia.edu/tag/07GE>
-/
def trivial : Pretopology C
    where
  coverings X S := ∃ (Y : _)(f : Y ⟶ X)(h : IsIso f), S = Presieve.singleton f
  has_isos X Y f i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine' ⟨pullback g f, pullback.snd, _, _⟩
    · skip
      refine' ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨_, by tidy⟩⟩⟩
      apply pullback.hom_ext
      · rw [assoc, pullback.lift_fst, ← pullback.condition_assoc]
        simp
      · simp
    · apply pullback_singleton
  Transitive := by
    rintro X S Ti ⟨Z, g, i, rfl⟩ hS
    rcases hS g (singleton_self g) with ⟨Y, f, i, hTi⟩
    refine' ⟨_, f ≫ g, _, _⟩
    · skip
      infer_instance
    ext (W k)
    constructor
    · rintro ⟨V, h, k, ⟨_⟩, hh, rfl⟩
      rw [hTi] at hh
      cases hh
      apply singleton.mk
    · rintro ⟨_⟩
      refine' bind_comp g presieve.singleton.mk _
      rw [hTi]
      apply presieve.singleton.mk
#align category_theory.pretopology.trivial CategoryTheory.Pretopology.trivial
-/

instance : OrderBot (Pretopology C) where
  bot := trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    exact K.has_isos f

/- warning: category_theory.pretopology.to_grothendieck_bot -> CategoryTheory.Pretopology.toGrothendieck_bot is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1], Eq.{max (succ u2) (succ u1)} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CategoryTheory.Pretopology.toGrothendieck.{u1, u2} C _inst_1 _inst_2 (Bot.bot.{max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (OrderBot.toHasBot.{max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.hasLe.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.orderBot.{u1, u2} C _inst_1 _inst_2)))) (Bot.bot.{max u2 u1} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CompleteLattice.toHasBot.{max u2 u1} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CategoryTheory.GrothendieckTopology.completeLattice.{u1, u2} C _inst_1)))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Limits.HasPullbacks.{u1, u2} C _inst_1], Eq.{max (succ u2) (succ u1)} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CategoryTheory.Pretopology.toGrothendieck.{u1, u2} C _inst_1 _inst_2 (Bot.bot.{max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (OrderBot.toBot.{max u2 u1} (CategoryTheory.Pretopology.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.LE.{u1, u2} C _inst_1 _inst_2) (CategoryTheory.Pretopology.instOrderBotPretopologyLE.{u1, u2} C _inst_1 _inst_2)))) (Bot.bot.{max u2 u1} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CompleteLattice.toBot.{max u2 u1} (CategoryTheory.GrothendieckTopology.{u1, u2} C _inst_1) (CategoryTheory.GrothendieckTopology.instCompleteLatticeGrothendieckTopology.{u1, u2} C _inst_1)))
Case conversion may be inaccurate. Consider using '#align category_theory.pretopology.to_grothendieck_bot CategoryTheory.Pretopology.toGrothendieck_botₓ'. -/
/-- The trivial pretopology induces the trivial grothendieck topology. -/
theorem toGrothendieck_bot : toGrothendieck C ⊥ = ⊥ :=
  (gi C).gc.l_bot
#align category_theory.pretopology.to_grothendieck_bot CategoryTheory.Pretopology.toGrothendieck_bot

end Pretopology

end CategoryTheory

