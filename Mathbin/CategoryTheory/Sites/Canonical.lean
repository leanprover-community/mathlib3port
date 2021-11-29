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

-- error in CategoryTheory.Sites.Canonical: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `is_sheaf_for_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
theorem is_sheaf_for_bind
(P : «expr ⥤ »(«expr ᵒᵖ»(C), Type v))
(U : sieve X)
(B : ∀ {{Y}} {{f : «expr ⟶ »(Y, X)}}, U f → sieve Y)
(hU : presieve.is_sheaf_for P U)
(hB : ∀ {{Y}} {{f : «expr ⟶ »(Y, X)}} (hf : U f), presieve.is_sheaf_for P (B hf))
(hB' : ∀
 {{Y}}
 {{f : «expr ⟶ »(Y, X)}}
 (h : U f)
 {{Z}}
 (g : «expr ⟶ »(Z, Y)), presieve.is_separated_for P ((B h).pullback g)) : presieve.is_sheaf_for P (sieve.bind U B) :=
begin
  intros [ident s, ident hs],
  let [ident y] [":", expr ∀
   {{Y}}
   {{f : «expr ⟶ »(Y, X)}}
   (hf : U f), presieve.family_of_elements P (B hf)] [":=", expr λ Y f hf Z g hg, s _ (presieve.bind_comp _ _ hg)],
  have [ident hy] [":", expr ∀ {{Y}} {{f : «expr ⟶ »(Y, X)}} (hf : U f), (y hf).compatible] [],
  { intros [ident Y, ident f, ident H, ident Y₁, ident Y₂, ident Z, ident g₁, ident g₂, ident f₁, ident f₂, ident hf₁, ident hf₂, ident comm],
    apply [expr hs],
    apply [expr reassoc_of comm] },
  let [ident t] [":", expr presieve.family_of_elements P U] [":=", expr λ Y f hf, (hB hf).amalgamate (y hf) (hy hf)],
  have [ident ht] [":", expr ∀
   {{Y}}
   {{f : «expr ⟶ »(Y, X)}}
   (hf : U f), (y hf).is_amalgamation (t f hf)] [":=", expr λ Y f hf, (hB hf).is_amalgamation _],
  have [ident hT] [":", expr t.compatible] [],
  { rw [expr presieve.compatible_iff_sieve_compatible] [],
    intros [ident Z, ident W, ident f, ident h, ident hf],
    apply [expr (hB (U.downward_closed hf h)).is_separated_for.ext],
    intros [ident Y, ident l, ident hl],
    apply [expr (hB' hf «expr ≫ »(l, h)).ext],
    intros [ident M, ident m, ident hm],
    have [] [":", expr bind U B «expr ≫ »(m, «expr ≫ »(l, «expr ≫ »(h, f)))] [],
    { have [] [":", expr bind U B _] [":=", expr presieve.bind_comp f hf hm],
      simpa [] [] [] [] [] ["using", expr this] },
    transitivity [expr s «expr ≫ »(m, «expr ≫ »(l, «expr ≫ »(h, f))) this],
    { have [] [] [":=", expr ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)],
      rw ["[", expr op_comp, ",", expr functor_to_types.map_comp_apply, "]"] ["at", ident this],
      rw [expr this] [],
      change [expr «expr = »(s _ _, s _ _)] [] [],
      simp [] [] [] [] [] [] },
    { have [] [":", expr «expr = »(s _ _, _)] [":=", expr (ht hf _ hm).symm],
      simp [] [] ["only"] ["[", expr assoc, "]"] [] ["at", ident this],
      rw [expr this] [],
      simp [] [] [] [] [] [] } },
  refine [expr ⟨hU.amalgamate t hT, _, _⟩],
  { rintro [ident Z, "_", "⟨", ident Y, ",", ident f, ",", ident g, ",", ident hg, ",", ident hf, ",", ident rfl, "⟩"],
    rw ["[", expr op_comp, ",", expr functor_to_types.map_comp_apply, ",", expr presieve.is_sheaf_for.valid_glue _ _ _ hg, "]"] [],
    apply [expr ht hg _ hf] },
  { intros [ident y, ident hy],
    apply [expr hU.is_separated_for.ext],
    intros [ident Y, ident f, ident hf],
    apply [expr (hB hf).is_separated_for.ext],
    intros [ident Z, ident g, ident hg],
    rw ["[", "<-", expr functor_to_types.map_comp_apply, ",", "<-", expr op_comp, ",", expr hy _ (presieve.bind_comp _ _ hg), ",", expr hU.valid_glue _ _ hf, ",", expr ht hf _ hg, "]"] [] }
end

-- error in CategoryTheory.Sites.Canonical: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `finest_topology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
theorem is_sheaf_for_trans
(P : «expr ⥤ »(«expr ᵒᵖ»(C), Type v))
(R S : sieve X)
(hR : presieve.is_sheaf_for P R)
(hR' : ∀ {{Y}} {{f : «expr ⟶ »(Y, X)}} (hf : S f), presieve.is_separated_for P (R.pullback f))
(hS : ∀ {{Y}} {{f : «expr ⟶ »(Y, X)}} (hf : R f), presieve.is_sheaf_for P (S.pullback f)) : presieve.is_sheaf_for P S :=
begin
  have [] [":", expr «expr ≤ »((bind R (λ Y f hf, S.pullback f) : presieve X), S)] [],
  { rintros [ident Z, ident f, "⟨", ident W, ",", ident f, ",", ident g, ",", ident hg, ",", "(", ident hf, ":", expr S _, ")", ",", ident rfl, "⟩"],
    apply [expr hf] },
  apply [expr presieve.is_sheaf_for_subsieve_aux P this],
  apply [expr is_sheaf_for_bind _ _ _ hR hS],
  { intros [ident Y, ident f, ident hf, ident Z, ident g],
    dsimp [] [] [] [],
    rw ["<-", expr pullback_comp] [],
    apply [expr (hS (R.downward_closed hf _)).is_separated_for] },
  { intros [ident Y, ident f, ident hf],
    have [] [":", expr «expr = »(sieve.pullback f (bind R (λ
        (T)
        (k : «expr ⟶ »(T, X))
        (hf : R k), pullback k S)), R.pullback f)] [],
    { ext [] [ident Z, ident g] [],
      split,
      { rintro ["⟨", ident W, ",", ident k, ",", ident l, ",", ident hl, ",", "_", ",", ident comm, "⟩"],
        rw ["[", expr pullback_apply, ",", "<-", expr comm, "]"] [],
        simp [] [] [] ["[", expr hl, "]"] [] [] },
      { intro [ident a],
        refine [expr ⟨Z, «expr𝟙»() Z, _, a, _⟩],
        simp [] [] [] ["[", expr hf, "]"] [] [] } },
    rw [expr this] [],
    apply [expr hR' hf] }
end

-- error in CategoryTheory.Sites.Canonical: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf.

This is a special case of https://stacks.math.columbia.edu/tag/00Z9, but following a different
proof (see the comments there).
-/ def finest_topology_single (P : «expr ⥤ »(«expr ᵒᵖ»(C), Type v)) : grothendieck_topology C :=
{ sieves := λ X S, ∀ (Y) (f : «expr ⟶ »(Y, X)), presieve.is_sheaf_for P (S.pullback f),
  top_mem' := λ X Y f, begin
    rw [expr sieve.pullback_top] [],
    exact [expr presieve.is_sheaf_for_top_sieve P]
  end,
  pullback_stable' := λ X Y S f hS Z g, begin
    rw ["<-", expr pullback_comp] [],
    apply [expr hS]
  end,
  transitive' := λ X S hS R hR Z g, begin
    refine [expr is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _],
    { intros [ident Y, ident f, ident hf],
      rw ["<-", expr pullback_comp] [],
      apply [expr (hS _ _).is_separated_for] },
    { intros [ident Y, ident f, ident hf],
      have [] [] [":=", expr hR hf _ («expr𝟙»() _)],
      rw ["[", expr pullback_id, ",", expr pullback_comp, "]"] ["at", ident this],
      apply [expr this] }
  end }

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
  (hJ : ∀ P (_ : P ∈ Ps), presieve.is_sheaf J P) : J ≤ finest_topology Ps :=
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

