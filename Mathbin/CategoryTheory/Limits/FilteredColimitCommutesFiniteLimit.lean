import Mathbin.CategoryTheory.Limits.ColimitLimit

/-!
# Filtered colimits commute with finite limits.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimit_limit_to_limit_colimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/


universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits.Types

open CategoryTheory.Limits.Types.FilteredColimit

namespace CategoryTheory.Limits

variable {J K : Type v} [small_category J] [small_category K]

variable (F : J × K ⥤ Type v)

open CategoryTheory.prod

variable [is_filtered K]

section 

/-!
Injectivity doesn't need that we have finitely many morphisms in `J`,
only that there are finitely many objects.
-/


variable [Fintype J]

-- error in CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
-/ theorem colimit_limit_to_limit_colimit_injective : function.injective (colimit_limit_to_limit_colimit F) :=
begin
  classical,
  intros [ident x, ident y, ident h],
  obtain ["⟨", ident kx, ",", ident x, ",", ident rfl, "⟩", ":=", expr jointly_surjective' x],
  obtain ["⟨", ident ky, ",", ident y, ",", ident rfl, "⟩", ":=", expr jointly_surjective' y],
  dsimp [] [] [] ["at", ident x, ident y],
  replace [ident h] [] [":=", expr λ j, congr_arg (limit.π «expr ⋙ »(curry.obj F, colim) j) h],
  simp [] [] [] ["[", expr colimit_eq_iff, "]"] [] ["at", ident h],
  let [ident k] [] [":=", expr λ j, (h j).some],
  let [ident f] [":", expr ∀ j, «expr ⟶ »(kx, k j)] [":=", expr λ j, (h j).some_spec.some],
  let [ident g] [":", expr ∀ j, «expr ⟶ »(ky, k j)] [":=", expr λ j, (h j).some_spec.some_spec.some],
  have [ident w] [":", expr ∀
   j, «expr = »(F.map ((«expr𝟙»() j, f j) : «expr ⟶ »((j, kx), (j, k j))) (limit.π ((curry.obj «expr ⋙ »(swap K J, F)).obj kx) j x), F.map ((«expr𝟙»() j, g j) : «expr ⟶ »((j, ky), (j, k j))) (limit.π ((curry.obj «expr ⋙ »(swap K J, F)).obj ky) j y))] [":=", expr λ
   j, (h j).some_spec.some_spec.some_spec],
  let [ident O] [":", expr finset K] [":=", expr «expr ∪ »(finset.univ.image k, {kx, ky})],
  have [ident kxO] [":", expr «expr ∈ »(kx, O)] [":=", expr finset.mem_union.mpr (or.inr (by simp [] [] [] [] [] []))],
  have [ident kyO] [":", expr «expr ∈ »(ky, O)] [":=", expr finset.mem_union.mpr (or.inr (by simp [] [] [] [] [] []))],
  have [ident kjO] [":", expr ∀
   j, «expr ∈ »(k j, O)] [":=", expr λ j, finset.mem_union.mpr (or.inl (by simp [] [] [] [] [] []))],
  let [ident H] [":", expr finset «exprΣ' , »((X Y : K)
    (mX : «expr ∈ »(X, O))
    (mY : «expr ∈ »(Y, O)), «expr ⟶ »(X, Y))] [":=", expr «expr ∪ »(finset.univ.image (λ
     j : J, ⟨kx, k j, kxO, finset.mem_union.mpr (or.inl (by simp [] [] [] [] [] [])), f j⟩), finset.univ.image (λ
     j : J, ⟨ky, k j, kyO, finset.mem_union.mpr (or.inl (by simp [] [] [] [] [] [])), g j⟩))],
  obtain ["⟨", ident S, ",", ident T, ",", ident W, "⟩", ":=", expr is_filtered.sup_exists O H],
  have [ident fH] [":", expr ∀
   j, «expr ∈ »((⟨kx, k j, kxO, kjO j, f j⟩ : «exprΣ' , »((X Y : K)
     (mX : «expr ∈ »(X, O))
     (mY : «expr ∈ »(Y, O)), «expr ⟶ »(X, Y))), H)] [":=", expr λ
   j, finset.mem_union.mpr (or.inl (begin
       simp [] [] ["only"] ["[", expr true_and, ",", expr finset.mem_univ, ",", expr eq_self_iff_true, ",", expr exists_prop_of_true, ",", expr finset.mem_image, ",", expr heq_iff_eq, "]"] [] [],
       refine [expr ⟨j, rfl, _⟩],
       simp [] [] ["only"] ["[", expr heq_iff_eq, "]"] [] [],
       exact [expr ⟨rfl, rfl, rfl⟩]
     end))],
  have [ident gH] [":", expr ∀
   j, «expr ∈ »((⟨ky, k j, kyO, kjO j, g j⟩ : «exprΣ' , »((X Y : K)
     (mX : «expr ∈ »(X, O))
     (mY : «expr ∈ »(Y, O)), «expr ⟶ »(X, Y))), H)] [":=", expr λ
   j, finset.mem_union.mpr (or.inr (begin
       simp [] [] ["only"] ["[", expr true_and, ",", expr finset.mem_univ, ",", expr eq_self_iff_true, ",", expr exists_prop_of_true, ",", expr finset.mem_image, ",", expr heq_iff_eq, "]"] [] [],
       refine [expr ⟨j, rfl, _⟩],
       simp [] [] ["only"] ["[", expr heq_iff_eq, "]"] [] [],
       exact [expr ⟨rfl, rfl, rfl⟩]
     end))],
  apply [expr colimit_sound' (T kxO) (T kyO)],
  ext [] [] [],
  simp [] [] ["only"] ["[", expr functor.comp_map, ",", expr limit.map_π_apply, ",", expr curry.obj_map_app, ",", expr swap_map, "]"] [] [],
  rw ["<-", expr W _ _ (fH j)] [],
  rw ["<-", expr W _ _ (gH j)] [],
  simp [] [] [] ["[", expr w, "]"] [] []
end

end 

variable [fin_category J]

-- error in CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
although with different names.
-/ theorem colimit_limit_to_limit_colimit_surjective : function.surjective (colimit_limit_to_limit_colimit F) :=
begin
  classical,
  intro [ident x],
  have [ident z] [] [":=", expr λ j, jointly_surjective' (limit.π «expr ⋙ »(curry.obj F, limits.colim) j x)],
  let [ident k] [":", expr J → K] [":=", expr λ j, (z j).some],
  let [ident y] [":", expr ∀ j, F.obj (j, k j)] [":=", expr λ j, (z j).some_spec.some],
  have [ident e] [":", expr ∀
   j, «expr = »(colimit.ι ((curry.obj F).obj j) (k j) (y j), limit.π «expr ⋙ »(curry.obj F, limits.colim) j x)] [":=", expr λ
   j, (z j).some_spec.some_spec],
  clear_value [ident k, ident y],
  clear [ident z],
  let [ident k'] [":", expr K] [":=", expr is_filtered.sup (finset.univ.image k) «expr∅»()],
  have [ident g] [":", expr ∀
   j, «expr ⟶ »(k j, k')] [":=", expr λ
   j, is_filtered.to_sup (finset.univ.image k) «expr∅»() (by simp [] [] [] [] [] [])],
  clear_value [ident k'],
  have [ident w] [":", expr ∀
   {j j' : J}
   (f : «expr ⟶ »(j, j')), «expr = »(colimit.ι ((curry.obj F).obj j') k' (F.map ((«expr𝟙»() j', g j') : «expr ⟶ »((j', k j'), (j', k'))) (y j')), colimit.ι ((curry.obj F).obj j') k' (F.map ((f, g j) : «expr ⟶ »((j, k j), (j', k'))) (y j)))] [],
  { intros [ident j, ident j', ident f],
    have [ident t] [":", expr «expr = »((f, g j), («expr ≫ »(((f, «expr𝟙»() (k j)) : «expr ⟶ »((j, k j), (j', k j))), («expr𝟙»() j', g j)) : «expr ⟶ »((j, k j), (j', k'))))] [],
    { simp [] [] ["only"] ["[", expr id_comp, ",", expr comp_id, ",", expr prod_comp, "]"] [] [] },
    erw ["[", expr colimit.w_apply, ",", expr t, ",", expr functor_to_types.map_comp_apply, ",", expr colimit.w_apply, ",", expr e, ",", "<-", expr limit.w_apply f, ",", "<-", expr e, "]"] [],
    simp [] [] [] [] [] [] },
  simp_rw [expr colimit_eq_iff] ["at", ident w],
  let [ident kf] [":", expr ∀ {j j'} (f : «expr ⟶ »(j, j')), K] [":=", expr λ _ _ f, (w f).some],
  let [ident gf] [":", expr ∀
   {j j'}
   (f : «expr ⟶ »(j, j')), «expr ⟶ »(k', kf f)] [":=", expr λ _ _ f, (w f).some_spec.some],
  let [ident hf] [":", expr ∀
   {j j'}
   (f : «expr ⟶ »(j, j')), «expr ⟶ »(k', kf f)] [":=", expr λ _ _ f, (w f).some_spec.some_spec.some],
  have [ident wf] [":", expr ∀
   {j j'}
   (f : «expr ⟶ »(j, j')), «expr = »(F.map ((«expr𝟙»() j', «expr ≫ »(g j', gf f)) : «expr ⟶ »((j', k j'), (j', kf f))) (y j'), F.map ((f, «expr ≫ »(g j, hf f)) : «expr ⟶ »((j, k j), (j', kf f))) (y j))] [":=", expr λ
   j j' f, begin
     have [ident q] [":", expr «expr = »(((curry.obj F).obj j').map (gf f) (F.map _ (y j')), ((curry.obj F).obj j').map (hf f) (F.map _ (y j)))] [":=", expr (w f).some_spec.some_spec.some_spec],
     dsimp [] [] [] ["at", ident q],
     simp_rw ["<-", expr functor_to_types.map_comp_apply] ["at", ident q],
     convert [] [expr q] []; simp [] [] ["only"] ["[", expr comp_id, "]"] [] []
   end],
  clear_value [ident kf, ident gf, ident hf],
  clear [ident w],
  let [ident O] [] [":=", expr «expr ∪ »(finset.univ.bUnion (λ
     j, finset.univ.bUnion (λ j', finset.univ.image (@kf j j'))), {k'})],
  have [ident kfO] [":", expr ∀
   {j j'}
   (f : «expr ⟶ »(j, j')), «expr ∈ »(kf f, O)] [":=", expr λ
   j
   j'
   f, finset.mem_union.mpr (or.inl (begin
       rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨j, finset.mem_univ j, _⟩],
       rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨j', finset.mem_univ j', _⟩],
       rw ["[", expr finset.mem_image, "]"] [],
       refine [expr ⟨f, finset.mem_univ _, _⟩],
       refl
     end))],
  have [ident k'O] [":", expr «expr ∈ »(k', O)] [":=", expr finset.mem_union.mpr (or.inr (finset.mem_singleton.mpr rfl))],
  let [ident H] [":", expr finset «exprΣ' , »((X Y : K)
    (mX : «expr ∈ »(X, O))
    (mY : «expr ∈ »(Y, O)), «expr ⟶ »(X, Y))] [":=", expr finset.univ.bUnion (λ
    j : J, finset.univ.bUnion (λ
     j' : J, finset.univ.bUnion (λ
      f : «expr ⟶ »(j, j'), {⟨k', kf f, k'O, kfO f, gf f⟩, ⟨k', kf f, k'O, kfO f, hf f⟩})))],
  obtain ["⟨", ident k'', ",", ident i', ",", ident s', "⟩", ":=", expr is_filtered.sup_exists O H],
  let [ident i] [":", expr ∀ {j j'} (f : «expr ⟶ »(j, j')), «expr ⟶ »(kf f, k'')] [":=", expr λ j j' f, i' (kfO f)],
  have [ident s] [":", expr ∀
   {j₁ j₂ j₃ j₄}
   (f : «expr ⟶ »(j₁, j₂))
   (f' : «expr ⟶ »(j₃, j₄)), «expr = »(«expr ≫ »(gf f, i f), «expr ≫ »(hf f', i f'))] [":=", expr begin
     intros [],
     rw ["[", expr s', ",", expr s', "]"] [],
     swap 2,
     exact [expr k'O],
     swap 2,
     { rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨j₁, finset.mem_univ _, _⟩],
       rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨j₂, finset.mem_univ _, _⟩],
       rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨f, finset.mem_univ _, _⟩],
       simp [] [] ["only"] ["[", expr true_or, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr finset.mem_insert, ",", expr heq_iff_eq, "]"] [] [] },
     { rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨j₃, finset.mem_univ _, _⟩],
       rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨j₄, finset.mem_univ _, _⟩],
       rw ["[", expr finset.mem_bUnion, "]"] [],
       refine [expr ⟨f', finset.mem_univ _, _⟩],
       simp [] [] ["only"] ["[", expr eq_self_iff_true, ",", expr or_true, ",", expr and_self, ",", expr finset.mem_insert, ",", expr finset.mem_singleton, ",", expr heq_iff_eq, "]"] [] [] }
   end],
  clear_value [ident i],
  clear [ident s', ident i', ident H, ident kfO, ident k'O, ident O],
  fsplit,
  { apply [expr colimit.ι «expr ⋙ »(curry.obj «expr ⋙ »(swap K J, F), limits.lim) k'' _],
    dsimp [] [] [] [],
    ext [] [] [],
    swap,
    { exact [expr λ
       j, F.map (⟨«expr𝟙»() j, «expr ≫ »(g j, «expr ≫ »(gf («expr𝟙»() j), i («expr𝟙»() j)))⟩ : «expr ⟶ »((j, k j), (j, k''))) (y j)] },
    { dsimp [] [] [] [],
      simp [] [] ["only"] ["[", "<-", expr functor_to_types.map_comp_apply, ",", expr prod_comp, ",", expr id_comp, ",", expr comp_id, "]"] [] [],
      calc
        «expr = »(F.map ((f, «expr ≫ »(g j, «expr ≫ »(gf («expr𝟙»() j), i («expr𝟙»() j)))) : «expr ⟶ »((j, k j), (j', k''))) (y j), F.map ((f, «expr ≫ »(g j, «expr ≫ »(hf f, i f))) : «expr ⟶ »((j, k j), (j', k''))) (y j)) : by rw [expr s («expr𝟙»() j) f] []
        «expr = »(..., F.map ((«expr𝟙»() j', i f) : «expr ⟶ »((j', kf f), (j', k''))) (F.map ((f, «expr ≫ »(g j, hf f)) : «expr ⟶ »((j, k j), (j', kf f))) (y j))) : by rw ["[", "<-", expr functor_to_types.map_comp_apply, ",", expr prod_comp, ",", expr comp_id, ",", expr assoc, "]"] []
        «expr = »(..., F.map ((«expr𝟙»() j', i f) : «expr ⟶ »((j', kf f), (j', k''))) (F.map ((«expr𝟙»() j', «expr ≫ »(g j', gf f)) : «expr ⟶ »((j', k j'), (j', kf f))) (y j'))) : by rw ["<-", expr wf f] []
        «expr = »(..., F.map ((«expr𝟙»() j', «expr ≫ »(g j', «expr ≫ »(gf f, i f))) : «expr ⟶ »((j', k j'), (j', k''))) (y j')) : by rw ["[", "<-", expr functor_to_types.map_comp_apply, ",", expr prod_comp, ",", expr id_comp, ",", expr assoc, "]"] []
        «expr = »(..., F.map ((«expr𝟙»() j', «expr ≫ »(g j', «expr ≫ »(gf («expr𝟙»() j'), i («expr𝟙»() j')))) : «expr ⟶ »((j', k j'), (j', k''))) (y j')) : by rw ["[", expr s f («expr𝟙»() j'), ",", "<-", expr s («expr𝟙»() j') («expr𝟙»() j'), "]"] [] } },
  { apply [expr limit_ext],
    intro [ident j],
    simp [] [] ["only"] ["[", "<-", expr e, ",", expr colimit_eq_iff, ",", expr curry.obj_obj_map, ",", expr limit.π_mk, ",", expr bifunctor.map_id_comp, ",", expr id.def, ",", expr types_comp_apply, ",", expr limits.ι_colimit_limit_to_limit_colimit_π_apply, "]"] [] [],
    refine [expr ⟨k'', «expr𝟙»() k'', «expr ≫ »(g j, «expr ≫ »(gf («expr𝟙»() j), i («expr𝟙»() j))), _⟩],
    simp [] [] ["only"] ["[", expr bifunctor.map_id_comp, ",", expr types_comp_apply, ",", expr bifunctor.map_id, ",", expr types_id_apply, "]"] [] [] }
end

instance colimit_limit_to_limit_colimit_is_iso : is_iso (colimit_limit_to_limit_colimit F) :=
  (is_iso_iff_bijective _).mpr ⟨colimit_limit_to_limit_colimit_injective F, colimit_limit_to_limit_colimit_surjective F⟩

-- error in CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance colimit_limit_to_limit_colimit_cone_iso
(F : «expr ⥤ »(J, «expr ⥤ »(K, Type v))) : is_iso (colimit_limit_to_limit_colimit_cone F) :=
begin
  haveI [] [":", expr is_iso (colimit_limit_to_limit_colimit_cone F).hom] [],
  { dsimp ["only"] ["[", expr colimit_limit_to_limit_colimit_cone, "]"] [] [],
    apply_instance },
  apply [expr cones.cone_iso_of_hom_iso]
end

noncomputable instance filtered_colim_preserves_finite_limit : preserves_limits_of_shape J (colim : (K ⥤ Type v) ⥤ _) :=
  ⟨fun F =>
      ⟨fun c hc =>
          by 
            apply is_limit.of_iso_limit (limit.is_limit _)
            symm 
            trans colim.map_cone (limit.cone F)
            exact functor.map_iso _ (hc.unique_up_to_iso (limit.is_limit F))
            exact as_iso (colimit_limit_to_limit_colimit_cone F)⟩⟩

end CategoryTheory.Limits

