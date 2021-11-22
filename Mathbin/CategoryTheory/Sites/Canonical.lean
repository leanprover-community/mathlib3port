import Mathbin.CategoryTheory.Sites.SheafOfTypes

/-!
# The canonical topology on a category

We define the finest (largest) Grothendieck topology for which a given presheaf `P` is a sheaf.
This is well defined since if `P` is a sheaf for a topology `J`, then it is a sheaf for any
coarser (smaller) topology. Nonetheless we define the topology explicitly by specifying its sieves:
A sieve `S` on `X` is covering for `finest_topology_single P` iff
  for any `f : Y ⟶ X`, `P` satisfies the sheaf axiom for `S.pullback f`.
Showing that this is a genuine Grothendieck topology (namely that it satisfies the transitivity
axiom) forms the bulk of this file.

This generalises to a set of presheaves, giving the topology `finest_topology Ps` which is the
finest topology for which every presheaf in `Ps` is a sheaf.
Using `Ps` as the set of representable presheaves defines the `canonical_topology`: the finest
topology for which every representable is a sheaf.

A Grothendieck topology is called `subcanonical` if it is smaller than the canonical topology,
equivalently it is subcanonical iff every representable presheaf is a sheaf.

## References
* https://ncatlab.org/nlab/show/canonical+topology
* https://ncatlab.org/nlab/show/subcanonical+coverage
* https://stacks.math.columbia.edu/tag/00Z9
* https://math.stackexchange.com/a/358709/
-/


universe v u

namespace CategoryTheory

open CategoryTheory Category Limits Sieve Classical

variable{C : Type u}[category.{v} C]

namespace Sheaf

variable{P : «expr ᵒᵖ» C ⥤ Type v}

variable{X Y : C}{S : sieve X}{R : presieve X}

variable(J J₂ : grothendieck_topology C)

/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `is_sheaf_for_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
theorem is_sheaf_for_bind (P : «expr ᵒᵖ» C ⥤ Type v) (U : sieve X) (B : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → sieve Y)
  (hU : presieve.is_sheaf_for P U) (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ hf : U f, presieve.is_sheaf_for P (B hf))
  (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ h : U f ⦃Z⦄ g : Z ⟶ Y, presieve.is_separated_for P ((B h).pullback g)) :
  presieve.is_sheaf_for P (sieve.bind U B) :=
  by 
    intro s hs 
    let y : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ hf : U f, presieve.family_of_elements P (B hf) :=
      fun Y f hf Z g hg => s _ (presieve.bind_comp _ _ hg)
    have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ hf : U f, (y hf).Compatible
    ·
      intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm 
      apply hs 
      apply reassoc_of comm 
    let t : presieve.family_of_elements P U := fun Y f hf => (hB hf).amalgamate (y hf) (hy hf)
    have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ hf : U f, (y hf).IsAmalgamation (t f hf) := fun Y f hf => (hB hf).IsAmalgamation _ 
    have hT : t.compatible
    ·
      rw [presieve.compatible_iff_sieve_compatible]
      intro Z W f h hf 
      apply (hB (U.downward_closed hf h)).IsSeparatedFor.ext 
      intro Y l hl 
      apply (hB' hf (l ≫ h)).ext 
      intro M m hm 
      have  : bind U B (m ≫ l ≫ h ≫ f)
      ·
        have  : bind U B _ := presieve.bind_comp f hf hm 
        simpa using this 
      trans s (m ≫ l ≫ h ≫ f) this
      ·
        have  := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)
        rw [op_comp, functor_to_types.map_comp_apply] at this 
        rw [this]
        change s _ _ = s _ _ 
        simp 
      ·
        have  : s _ _ = _ := (ht hf _ hm).symm 
        simp only [assoc] at this 
        rw [this]
        simp 
    refine' ⟨hU.amalgamate t hT, _, _⟩
    ·
      rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩
      rw [op_comp, functor_to_types.map_comp_apply, presieve.is_sheaf_for.valid_glue _ _ _ hg]
      apply ht hg _ hf
    ·
      intro y hy 
      apply hU.is_separated_for.ext 
      intro Y f hf 
      apply (hB hf).IsSeparatedFor.ext 
      intro Z g hg 
      rw [←functor_to_types.map_comp_apply, ←op_comp, hy _ (presieve.bind_comp _ _ hg), hU.valid_glue _ _ hf,
        ht hf _ hg]

/--
Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `finest_topology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
theorem is_sheaf_for_trans (P : «expr ᵒᵖ» C ⥤ Type v) (R S : sieve X) (hR : presieve.is_sheaf_for P R)
  (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ hf : S f, presieve.is_separated_for P (R.pullback f))
  (hS : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ hf : R f, presieve.is_sheaf_for P (S.pullback f)) : presieve.is_sheaf_for P S :=
  by 
    have  : (bind R fun Y f hf => S.pullback f : presieve X) ≤ S
    ·
      rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
      apply hf 
    apply presieve.is_sheaf_for_subsieve_aux P this 
    apply is_sheaf_for_bind _ _ _ hR hS
    ·
      intro Y f hf Z g 
      dsimp 
      rw [←pullback_comp]
      apply (hS (R.downward_closed hf _)).IsSeparatedFor
    ·
      intro Y f hf 
      have  : sieve.pullback f (bind R fun T k : T ⟶ X hf : R k => pullback k S) = R.pullback f
      ·
        ext Z g 
        split 
        ·
          rintro ⟨W, k, l, hl, _, comm⟩
          rw [pullback_apply, ←comm]
          simp [hl]
        ·
          intro a 
          refine' ⟨Z, 𝟙 Z, _, a, _⟩
          simp [hf]
      rw [this]
      apply hR' hf

/--
Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf.

This is a special case of https://stacks.math.columbia.edu/tag/00Z9, but following a different
proof (see the comments there).
-/
def finest_topology_single (P : «expr ᵒᵖ» C ⥤ Type v) : grothendieck_topology C :=
  { Sieves := fun X S => ∀ Y f : Y ⟶ X, presieve.is_sheaf_for P (S.pullback f),
    top_mem' :=
      fun X Y f =>
        by 
          rw [sieve.pullback_top]
          exact presieve.is_sheaf_for_top_sieve P,
    pullback_stable' :=
      fun X Y S f hS Z g =>
        by 
          rw [←pullback_comp]
          apply hS,
    transitive' :=
      fun X S hS R hR Z g =>
        by 
          refine' is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _
          ·
            intro Y f hf 
            rw [←pullback_comp]
            apply (hS _ _).IsSeparatedFor
          ·
            intro Y f hf 
            have  := hR hf _ (𝟙 _)
            rw [pullback_id, pullback_comp] at this 
            apply this }

/--
Construct the finest (largest) Grothendieck topology for which all the given presheaves are sheaves.

This is equal to the construction of https://stacks.math.columbia.edu/tag/00Z9.
-/
def finest_topology (Ps : Set («expr ᵒᵖ» C ⥤ Type v)) : grothendieck_topology C :=
  Inf (finest_topology_single '' Ps)

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
theorem sheaf_for_finest_topology (Ps : Set («expr ᵒᵖ» C ⥤ Type v)) (h : P ∈ Ps) :
  presieve.is_sheaf (finest_topology Ps) P :=
  fun X S hS =>
    by 
      simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finest_topology Ps`.
-/
theorem le_finest_topology (Ps : Set («expr ᵒᵖ» C ⥤ Type v)) (J : grothendieck_topology C)
  (hJ : ∀ P _ : P ∈ Ps, presieve.is_sheaf J P) : J ≤ finest_topology Ps :=
  by 
    rintro X S hS _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
    intro Y f 
    exact hJ P hP (S.pullback f) (J.pullback_stable f hS)

/--
The `canonical_topology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf.

See https://stacks.math.columbia.edu/tag/00ZA
-/
def canonical_topology (C : Type u) [category.{v} C] : grothendieck_topology C :=
  finest_topology (Set.Range yoneda.obj)

/-- `yoneda.obj X` is a sheaf for the canonical topology. -/
theorem is_sheaf_yoneda_obj (X : C) : presieve.is_sheaf (canonical_topology C) (yoneda.obj X) :=
  fun Y S hS => sheaf_for_finest_topology _ (Set.mem_range_self _) _ hS

/-- A representable functor is a sheaf for the canonical topology. -/
theorem is_sheaf_of_representable (P : «expr ᵒᵖ» C ⥤ Type v) [P.representable] :
  presieve.is_sheaf (canonical_topology C) P :=
  presieve.is_sheaf_iso (canonical_topology C) P.repr_w (is_sheaf_yoneda_obj _)

/--
A subcanonical topology is a topology which is smaller than the canonical topology.
Equivalently, a topology is subcanonical iff every representable is a sheaf.
-/
def subcanonical (J : grothendieck_topology C) : Prop :=
  J ≤ canonical_topology C

namespace Subcanonical

/-- If every functor `yoneda.obj X` is a `J`-sheaf, then `J` is subcanonical. -/
theorem of_yoneda_is_sheaf (J : grothendieck_topology C) (h : ∀ X, presieve.is_sheaf J (yoneda.obj X)) :
  subcanonical J :=
  le_finest_topology _ _
    (by 
      rintro P ⟨X, rfl⟩
      apply h)

/-- If `J` is subcanonical, then any representable is a `J`-sheaf. -/
theorem is_sheaf_of_representable {J : grothendieck_topology C} (hJ : subcanonical J) (P : «expr ᵒᵖ» C ⥤ Type v)
  [P.representable] : presieve.is_sheaf J P :=
  presieve.is_sheaf_of_le _ hJ (is_sheaf_of_representable P)

end Subcanonical

end Sheaf

end CategoryTheory

