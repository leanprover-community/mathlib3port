import Mathbin.CategoryTheory.Sites.Plus 
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!

# Sheafification

We construct the sheafification of a presheaf over a site `C` with values in `D` whenever
`D` is a concrete category for which the forgetful functor preserves the appropriate (co)limits
and reflects isomorphisms.

We generally follow the approach of https://stacks.math.columbia.edu/tag/00W1

-/


namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe w v u

variable{C : Type u}[category.{v} C]{J : grothendieck_topology C}

variable{D : Type w}[category.{max v u} D]

section 

variable[concrete_category.{max v u} D]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

/-- A concrete version of the multiequalizer, to be used below. -/
@[nolint has_inhabited_instance]
def meq {X : C} (P : «expr ᵒᵖ» C ⥤ D) (S : J.cover X) :=
  { x : ∀ I : S.arrow, P.obj (op I.Y) // ∀ I : S.relation, P.map I.g₁.op (x I.fst) = P.map I.g₂.op (x I.snd) }

end 

namespace Meq

variable[concrete_category.{max v u} D]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

instance  {X} (P : «expr ᵒᵖ» C ⥤ D) (S : J.cover X) : CoeFun (meq P S) fun x => ∀ I : S.arrow, P.obj (op I.Y) :=
  ⟨fun x => x.1⟩

@[ext]
theorem ext {X} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} (x y : meq P S) (h : ∀ I : S.arrow, x I = y I) : x = y :=
  Subtype.ext$ funext$ h

theorem condition {X} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} (x : meq P S) (I : S.relation) :
  P.map I.g₁.op (x ((S.index P).fstTo I)) = P.map I.g₂.op (x ((S.index P).sndTo I)) :=
  x.2 _

/-- Refine a term of `meq P T` with respect to a refinement `S ⟶ T` of covers. -/
def refine {X : C} {P : «expr ᵒᵖ» C ⥤ D} {S T : J.cover X} (x : meq P T) (e : S ⟶ T) : meq P S :=
  ⟨fun I => x ⟨I.Y, I.f, (le_of_hom e) _ I.hf⟩,
    fun I => x.condition ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁, I.f₂, (le_of_hom e) _ I.h₁, (le_of_hom e) _ I.h₂, I.w⟩⟩

@[simp]
theorem refine_apply {X : C} {P : «expr ᵒᵖ» C ⥤ D} {S T : J.cover X} (x : meq P T) (e : S ⟶ T) (I : S.arrow) :
  x.refine e I = x ⟨I.Y, I.f, (le_of_hom e) _ I.hf⟩ :=
  rfl

/-- Pull back a term of `meq P S` with respect to a morphism `f : Y ⟶ X` in `C`. -/
def pullback {Y X : C} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X) : meq P ((J.pullback f).obj S) :=
  ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩,
    fun I =>
      x.condition
        ⟨I.Y₁, I.Y₂, I.Z, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂,
          by 
            simp [reassoc_of I.w]⟩⟩

@[simp]
theorem pullback_apply {Y X : C} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X)
  (I : ((J.pullback f).obj S).arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ :=
  rfl

@[simp]
theorem pullback_refine {Y X : C} {P : «expr ᵒᵖ» C ⥤ D} {S T : J.cover X} (h : S ⟶ T) (f : Y ⟶ X) (x : meq P T) :
  (x.pullback f).refine ((J.pullback f).map h) = (refine x h).pullback _ :=
  rfl

/-- Make a term of `meq P S`. -/
def mk {X : C} {P : «expr ᵒᵖ» C ⥤ D} (S : J.cover X) (x : P.obj (op X)) : meq P S :=
  ⟨fun I => P.map I.f.op x,
    fun I =>
      by 
        dsimp 
        simp only [←comp_apply, ←P.map_comp, ←op_comp, I.w]⟩

theorem mk_apply {X : C} {P : «expr ᵒᵖ» C ⥤ D} (S : J.cover X) (x : P.obj (op X)) (I : S.arrow) :
  mk S x I = P.map I.f.op x :=
  rfl

variable[preserves_limits (forget D)]

/-- The equivalence between the type associated to `multiequalizer (S.index P)` and `meq P S`. -/
noncomputable def Equiv {X : C} (P : «expr ᵒᵖ» C ⥤ D) (S : J.cover X) [has_multiequalizer (S.index P)] :
  (multiequalizer (S.index P) : D) ≃ meq P S :=
  limits.concrete.multiequalizer_equiv _

@[simp]
theorem equiv_apply {X : C} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} [has_multiequalizer (S.index P)]
  (x : multiequalizer (S.index P)) (I : S.arrow) : Equiv P S x I = multiequalizer.ι (S.index P) I x :=
  rfl

@[simp]
theorem equiv_symm_eq_apply {X : C} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} [has_multiequalizer (S.index P)] (x : meq P S)
  (I : S.arrow) : multiequalizer.ι (S.index P) I ((meq.equiv P S).symm x) = x I :=
  by 
    let z := (meq.equiv P S).symm x 
    rw [←equiv_apply]
    simp 

end Meq

namespace GrothendieckTopology

namespace Plus

variable[concrete_category.{max v u} D]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable[preserves_limits (forget D)]

variable[∀ X : C, has_colimits_of_shape («expr ᵒᵖ» (J.cover X)) D]

variable[∀ P : «expr ᵒᵖ» C ⥤ D X : C S : J.cover X, has_multiequalizer (S.index P)]

noncomputable theory

/-- Make a term of `(J.plus_obj P).obj (op X)` from `x : meq P S`. -/
def mk {X : C} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} (x : meq P S) : (J.plus_obj P).obj (op X) :=
  colimit.ι (J.diagram P X) (op S) ((meq.equiv P S).symm x)

theorem res_mk_eq_mk_pullback {Y X : C} {P : «expr ᵒᵖ» C ⥤ D} {S : J.cover X} (x : meq P S) (f : Y ⟶ X) :
  (J.plus_obj P).map f.op (mk x) = mk (x.pullback f) :=
  by 
    dsimp [mk]
    simp only [←comp_apply, colimit.ι_pre, ι_colim_map_assoc]
    simpRw [comp_apply]
    congr 1
    applyFun meq.equiv P _ 
    erw [Equiv.apply_symm_apply]
    ext i 
    simp only [diagram_pullback_app, meq.pullback_apply, meq.equiv_apply, ←comp_apply]
    erw [multiequalizer.lift_ι, meq.equiv_symm_eq_apply]
    cases i 
    rfl

theorem to_plus_mk {X : C} {P : «expr ᵒᵖ» C ⥤ D} (S : J.cover X) (x : P.obj (op X)) :
  (J.to_plus P).app _ x = mk (meq.mk S x) :=
  by 
    dsimp [mk]
    let e : S ⟶ ⊤ := hom_of_le (SemilatticeInfTop.le_top _)
    rw [←colimit.w _ e.op]
    delta' cover.to_multiequalizer 
    simp only [comp_apply]
    congr 1
    dsimp [diagram]
    apply concrete.multiequalizer_ext 
    intro i 
    simpa only [←comp_apply, category.assoc, multiequalizer.lift_ι, category.comp_id, meq.equiv_symm_eq_apply]

theorem to_plus_apply {X : C} {P : «expr ᵒᵖ» C ⥤ D} (S : J.cover X) (x : meq P S) (I : S.arrow) :
  (J.to_plus P).app _ (x I) = (J.plus_obj P).map I.f.op (mk x) :=
  by 
    dsimp only [to_plus]
    delta' cover.to_multiequalizer 
    dsimp [mk]
    simp only [←comp_apply, colimit.ι_pre, ι_colim_map_assoc]
    simp only [comp_apply]
    dsimp only [functor.op]
    let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := hom_of_le (SemilatticeInfTop.le_top _)
    rw [←colimit.w _ e.op]
    simp only [comp_apply]
    congr 1
    apply concrete.multiequalizer_ext 
    intro i 
    dsimp [diagram]
    simp only [←comp_apply, category.assoc, multiequalizer.lift_ι, category.comp_id, meq.equiv_symm_eq_apply]
    let RR : S.relation :=
      ⟨_, _, _, i.f, 𝟙 _, I.f, i.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _,
        by 
          simp ⟩
    cases I 
    erw [x.condition RR]
    simpa [RR]

theorem to_plus_eq_mk {X : C} {P : «expr ᵒᵖ» C ⥤ D} (x : P.obj (op X)) : (J.to_plus P).app _ x = mk (meq.mk ⊤ x) :=
  by 
    dsimp [mk]
    delta' cover.to_multiequalizer 
    simp only [comp_apply]
    congr 1
    applyFun meq.equiv P ⊤
    ext i 
    simpa

variable[∀ X : C, preserves_colimits_of_shape («expr ᵒᵖ» (J.cover X)) (forget D)]

theorem exists_rep {X : C} {P : «expr ᵒᵖ» C ⥤ D} (x : (J.plus_obj P).obj (op X)) :
  ∃ (S : J.cover X)(y : meq P S), x = mk y :=
  by 
    obtain ⟨S, y, h⟩ := concrete.colimit_exists_rep (J.diagram P X) x 
    use S.unop, meq.equiv _ _ y 
    rw [←h]
    dsimp [mk]
    simp 

theorem eq_mk_iff_exists {X : C} {P : «expr ᵒᵖ» C ⥤ D} {S T : J.cover X} (x : meq P S) (y : meq P T) :
  mk x = mk y ↔ ∃ (W : J.cover X)(h1 : W ⟶ S)(h2 : W ⟶ T), x.refine h1 = y.refine h2 :=
  by 
    split 
    ·
      intro h 
      obtain ⟨W, h1, h2, hh⟩ := concrete.colimit_exists_of_rep_eq _ _ _ h 
      use W.unop, h1.unop, h2.unop 
      ext I 
      applyFun multiequalizer.ι (W.unop.index P) I  at hh 
      convert hh 
      all_goals 
        dsimp [diagram]
        simp only [←comp_apply, multiequalizer.lift_ι, category.comp_id, meq.equiv_symm_eq_apply]
        cases I 
        rfl
    ·
      rintro ⟨S, h1, h2, e⟩
      apply concrete.colimit_rep_eq_of_exists 
      use op S, h1.op, h2.op 
      apply concrete.multiequalizer_ext 
      intro i 
      applyFun fun ee => ee i  at e 
      convert e 
      all_goals 
        dsimp [diagram]
        simp only [←comp_apply, multiequalizer.lift_ι, meq.equiv_symm_eq_apply]
        cases i 
        rfl

-- error in CategoryTheory.Sites.Sheafification: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `P⁺` is always separated. -/
theorem sep
{X : C}
(P : «expr ⥤ »(«expr ᵒᵖ»(C), D))
(S : J.cover X)
(x y : (J.plus_obj P).obj (op X))
(h : ∀ I : S.arrow, «expr = »((J.plus_obj P).map I.f.op x, (J.plus_obj P).map I.f.op y)) : «expr = »(x, y) :=
begin
  obtain ["⟨", ident Sx, ",", ident x, ",", ident rfl, "⟩", ":=", expr exists_rep x],
  obtain ["⟨", ident Sy, ",", ident y, ",", ident rfl, "⟩", ":=", expr exists_rep y],
  simp [] [] ["only"] ["[", expr res_mk_eq_mk_pullback, "]"] [] ["at", ident h],
  choose [] [ident W] [ident h1, ident h2, ident hh] ["using", expr λ I : S.arrow, (eq_mk_iff_exists _ _).mp (h I)],
  rw [expr eq_mk_iff_exists] [],
  let [ident B] [":", expr J.cover X] [":=", expr S.bind W],
  use [expr B],
  let [ident ex] [":", expr «expr ⟶ »(B, Sx)] [":=", expr hom_of_le (begin
      rintros [ident Y, ident f, "⟨", ident Z, ",", ident e1, ",", ident e2, ",", ident he2, ",", ident he1, ",", ident hee, "⟩"],
      rw ["<-", expr hee] [],
      apply [expr le_of_hom (h1 ⟨_, _, he2⟩)],
      exact [expr he1]
    end)],
  let [ident ey] [":", expr «expr ⟶ »(B, Sy)] [":=", expr hom_of_le (begin
      rintros [ident Y, ident f, "⟨", ident Z, ",", ident e1, ",", ident e2, ",", ident he2, ",", ident he1, ",", ident hee, "⟩"],
      rw ["<-", expr hee] [],
      apply [expr le_of_hom (h2 ⟨_, _, he2⟩)],
      exact [expr he1]
    end)],
  use ["[", expr ex, ",", expr ey, "]"],
  ext1 [] [ident I],
  let [ident IS] [":", expr S.arrow] [":=", expr I.from_middle],
  specialize [expr hh IS],
  let [ident IW] [":", expr (W IS).arrow] [":=", expr I.to_middle],
  apply_fun [expr λ e, e IW] ["at", ident hh] [],
  convert [] [expr hh] [],
  { let [ident Rx] [":", expr Sx.relation] [":=", expr ⟨I.Y, I.Y, I.Y, «expr𝟙»() _, «expr𝟙»() _, I.f, «expr ≫ »(I.to_middle_hom, I.from_middle_hom), _, _, by simp [] [] [] ["[", expr I.middle_spec, "]"] [] []⟩],
    have [] [] [":=", expr x.condition Rx],
    simpa [] [] [] [] [] ["using", expr this] },
  { let [ident Ry] [":", expr Sy.relation] [":=", expr ⟨I.Y, I.Y, I.Y, «expr𝟙»() _, «expr𝟙»() _, I.f, «expr ≫ »(I.to_middle_hom, I.from_middle_hom), _, _, by simp [] [] [] ["[", expr I.middle_spec, "]"] [] []⟩],
    have [] [] [":=", expr y.condition Ry],
    simpa [] [] [] [] [] ["using", expr this] }
end

theorem inj_of_sep (P : «expr ᵒᵖ» C ⥤ D)
  (hsep : ∀ X : C S : J.cover X x y : P.obj (op X), (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y) (X : C) :
  Function.Injective ((J.to_plus P).app (op X)) :=
  by 
    intro x y h 
    simp only [to_plus_eq_mk] at h 
    rw [eq_mk_iff_exists] at h 
    obtain ⟨W, h1, h2, hh⟩ := h 
    apply hsep X W 
    intro I 
    applyFun fun e => e I  at hh 
    exact hh

/-- An auxiliary definition to be used in the proof of `exists_of_sep` below.
  Given a compatible family of local sections for `P⁺`, and representatives of said sections,
  construct a compatible family of local sections of `P` over the combination of the covers
  associated to the representatives.
  The separatedness condition is used to prove compatibility among these local sections of `P`. -/
def meq_of_sep (P : «expr ᵒᵖ» C ⥤ D)
  (hsep : ∀ X : C S : J.cover X x y : P.obj (op X), (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y) (X : C)
  (S : J.cover X) (s : meq (J.plus_obj P) S) (T : ∀ I : S.arrow, J.cover I.Y) (t : ∀ I : S.arrow, meq P (T I))
  (ht : ∀ I : S.arrow, s I = mk (t I)) : meq P (S.bind T) :=
  { val := fun I => t I.from_middle I.to_middle,
    property :=
      by 
        intro II 
        apply inj_of_sep P hsep 
        rw [←comp_apply, ←comp_apply, (J.to_plus P).naturality, (J.to_plus P).naturality, comp_apply, comp_apply]
        erw [to_plus_apply (T II.fst.from_middle) (t II.fst.from_middle) II.fst.to_middle,
          to_plus_apply (T II.snd.from_middle) (t II.snd.from_middle) II.snd.to_middle, ←ht, ←ht, ←comp_apply,
          ←comp_apply, ←(J.plus_obj P).map_comp, ←(J.plus_obj P).map_comp]
        rw [←op_comp, ←op_comp]
        let IR : S.relation :=
          ⟨_, _, _, II.g₁ ≫ II.fst.to_middle_hom, II.g₂ ≫ II.snd.to_middle_hom, II.fst.from_middle_hom,
            II.snd.from_middle_hom, II.fst.from_middle_condition, II.snd.from_middle_condition, _⟩
        swap
        ·
          simp only [category.assoc, II.fst.middle_spec, II.snd.middle_spec]
          apply II.w 
        exact s.condition IR }

-- error in CategoryTheory.Sites.Sheafification: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_of_sep
(P : «expr ⥤ »(«expr ᵒᵖ»(C), D))
(hsep : ∀
 (X : C)
 (S : J.cover X)
 (x y : P.obj (op X)), ∀ I : S.arrow, «expr = »(P.map I.f.op x, P.map I.f.op y) → «expr = »(x, y))
(X : C)
(S : J.cover X)
(s : meq (J.plus_obj P) S) : «expr∃ , »((t : (J.plus_obj P).obj (op X)), «expr = »(meq.mk S t, s)) :=
begin
  have [ident inj] [":", expr ∀ X : C, function.injective ((J.to_plus P).app (op X))] [":=", expr inj_of_sep _ hsep],
  choose [] [ident T] [ident t, ident ht] ["using", expr λ I, exists_rep (s I)],
  let [ident B] [":", expr J.cover X] [":=", expr S.bind T],
  choose [] [ident Z] [ident e1, ident e2, ident he2, ident he1, ident hee] ["using", expr λ I : B.arrow, I.hf],
  let [ident w] [":", expr meq P B] [":=", expr meq_of_sep P hsep X S s T t ht],
  use [expr mk w],
  ext [] [ident I] [],
  erw ["[", expr ht, ",", expr res_mk_eq_mk_pullback, "]"] [],
  apply [expr sep P (T I)],
  intros [ident II],
  simp [] [] ["only"] ["[", expr res_mk_eq_mk_pullback, ",", expr eq_mk_iff_exists, "]"] [] [],
  use [expr (J.pullback II.f).obj (T I)],
  let [ident e0] [":", expr «expr ⟶ »((J.pullback II.f).obj (T I), (J.pullback II.f).obj ((J.pullback I.f).obj B))] [":=", expr hom_of_le (begin
      intros [ident Y, ident f, ident hf],
      apply [expr sieve.le_pullback_bind _ _ _ I.hf],
      { cases [expr I] [],
        exact [expr hf] }
    end)],
  use ["[", expr e0, ",", expr «expr𝟙»() _, "]"],
  ext [] [ident IV] [],
  dsimp ["only"] ["[", expr meq.refine_apply, ",", expr meq.pullback_apply, ",", expr w, "]"] [] [],
  let [ident IA] [":", expr B.arrow] [":=", expr ⟨_, «expr ≫ »(«expr ≫ »(IV.f, II.f), I.f), _⟩],
  swap,
  { refine [expr ⟨I.Y, _, _, I.hf, _, rfl⟩],
    apply [expr sieve.downward_closed],
    convert [] [expr II.hf] [],
    cases [expr I] [],
    refl },
  let [ident IB] [":", expr S.arrow] [":=", expr IA.from_middle],
  let [ident IC] [":", expr (T IB).arrow] [":=", expr IA.to_middle],
  let [ident ID] [":", expr (T I).arrow] [":=", expr ⟨IV.Y, «expr ≫ »(IV.f, II.f), sieve.downward_closed (T I) II.hf IV.f⟩],
  change [expr «expr = »(t IB IC, t I ID)] [] [],
  apply [expr inj IV.Y],
  erw ["[", expr to_plus_apply (T I) (t I) ID, ",", expr to_plus_apply (T IB) (t IB) IC, ",", "<-", expr ht, ",", "<-", expr ht, "]"] [],
  let [ident IR] [":", expr S.relation] [":=", expr ⟨_, _, IV.Y, IC.f, ID.f, IB.f, I.f, _, I.hf, IA.middle_spec⟩],
  convert [] [expr s.condition IR] [],
  cases [expr I] [],
  refl
end

variable[reflects_isomorphisms (forget D)]

/-- If `P` is separated, then `P⁺` is a sheaf. -/
theorem is_sheaf_of_sep (P : «expr ᵒᵖ» C ⥤ D)
  (hsep : ∀ X : C S : J.cover X x y : P.obj (op X), (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y) :
  presheaf.is_sheaf J (J.plus_obj P) :=
  by 
    rw [presheaf.is_sheaf_iff_multiequalizer]
    intro X S 
    apply is_iso_of_reflects_iso _ (forget D)
    rw [is_iso_iff_bijective]
    split 
    ·
      intro x y h 
      apply sep P S _ _ 
      intro I 
      applyFun meq.equiv _ _  at h 
      applyFun fun e => e I  at h 
      convert h
      ·
        erw [meq.equiv_apply, ←comp_apply, multiequalizer.lift_ι]
      ·
        erw [meq.equiv_apply, ←comp_apply, multiequalizer.lift_ι]
    ·
      rintro (x : (multiequalizer (S.index _) : D))
      obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (meq.equiv _ _ x)
      use t 
      applyFun meq.equiv _ _ 
      swap
      ·
        infer_instance 
      rw [←ht]
      ext i 
      dsimp 
      rw [←comp_apply, multiequalizer.lift_ι]
      rfl

variable(J)

/-- `P⁺⁺` is always a sheaf. -/
theorem is_sheaf_plus_plus (P : «expr ᵒᵖ» C ⥤ D) : presheaf.is_sheaf J (J.plus_obj (J.plus_obj P)) :=
  by 
    apply is_sheaf_of_sep 
    intro X S x y 
    apply sep

end Plus

variable(J)

variable[∀ P : «expr ᵒᵖ» C ⥤ D X : C S : J.cover X,
      has_multiequalizer (S.index P)][∀ X : C, has_colimits_of_shape («expr ᵒᵖ» (J.cover X)) D]

/-- The sheafification of a presheaf `P`.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
@[simps]
def sheafify (P : «expr ᵒᵖ» C ⥤ D) : «expr ᵒᵖ» C ⥤ D :=
  J.plus_obj (J.plus_obj P)

/-- The canonical map from `P` to its sheafification. -/
@[simps]
def to_sheafify (P : «expr ᵒᵖ» C ⥤ D) : P ⟶ J.sheafify P :=
  J.to_plus P ≫ J.plus_map (J.to_plus P)

variable(D)

/-- The sheafification of a presheaf `P`, as a functor.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
@[simps map]
def sheafification : («expr ᵒᵖ» C ⥤ D) ⥤ «expr ᵒᵖ» C ⥤ D :=
  J.plus_functor D ⋙ J.plus_functor D

@[simp]
theorem sheafification_obj (P : «expr ᵒᵖ» C ⥤ D) : (J.sheafification D).obj P = J.sheafify P :=
  rfl

/-- The canonical map from `P` to its sheafification, as a natural transformation.
*Note:* We only show this is a sheaf under additional hypotheses on `D`. -/
def to_sheafification : 𝟭 _ ⟶ sheafification J D :=
  J.to_plus_nat_trans D ≫ whisker_right (J.to_plus_nat_trans D) (J.plus_functor D)

@[simp]
theorem to_sheafification_app (P : «expr ᵒᵖ» C ⥤ D) : (J.to_sheafification D).app P = J.to_sheafify P :=
  rfl

variable{D}

-- error in CategoryTheory.Sites.Sheafification: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_iso_to_sheafify {P : «expr ⥤ »(«expr ᵒᵖ»(C), D)} (hP : presheaf.is_sheaf J P) : is_iso (J.to_sheafify P) :=
begin
  dsimp [] ["[", expr to_sheafify, "]"] [] [],
  haveI [] [":", expr is_iso (J.to_plus P)] [":=", expr by { apply [expr is_iso_to_plus_of_is_sheaf J P hP] }],
  haveI [] [":", expr is_iso ((J.plus_functor D).map (J.to_plus P))] [":=", expr by { apply [expr functor.map_is_iso] }],
  exact [expr @is_iso.comp_is_iso _ _ _ _ _ (J.to_plus P) ((J.plus_functor D).map (J.to_plus P)) _ _]
end

-- error in CategoryTheory.Sites.Sheafification: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `P` is a sheaf, then `P` is isomorphic to `J.sheafify P`. -/
def iso_sheafify {P : «expr ⥤ »(«expr ᵒᵖ»(C), D)} (hP : presheaf.is_sheaf J P) : «expr ≅ »(P, J.sheafify P) :=
by letI [] [] [":=", expr is_iso_to_sheafify J hP]; exactI [expr as_iso (J.to_sheafify P)]

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from
`J.sheafifcation P` to `Q`. -/
def sheafify_lift {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) : J.sheafify P ⟶ Q :=
  J.plus_lift (J.plus_lift η hQ) hQ

theorem to_sheafify_sheafify_lift {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.to_sheafify P ≫ sheafify_lift J η hQ = η :=
  by 
    dsimp only [sheafify_lift, to_sheafify]
    rw [category.assoc, J.plus_map_to_plus P, to_plus_plus_lift, to_plus_plus_lift]

theorem sheafify_lift_unique {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) (γ : J.sheafify P ⟶ Q) :
  J.to_sheafify P ≫ γ = η → γ = sheafify_lift J η hQ :=
  by 
    intro h 
    apply plus_lift_unique 
    apply plus_lift_unique 
    rw [←category.assoc, ←plus_map_to_plus]
    exact h

theorem sheafify_hom_ext {P Q : «expr ᵒᵖ» C ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : presheaf.is_sheaf J Q)
  (h : J.to_sheafify P ≫ η = J.to_sheafify P ≫ γ) : η = γ :=
  by 
    apply J.plus_hom_ext _ _ hQ 
    apply J.plus_hom_ext _ _ hQ 
    rw [←category.assoc, ←category.assoc, ←plus_map_to_plus]
    exact h

end GrothendieckTopology

variable(J D)

variable[concrete_category.{max v u}
      D][preserves_limits
      (forget
        D)][∀ P : «expr ᵒᵖ» C ⥤ D X : C S : J.cover X,
      has_multiequalizer
        (S.index
          P)][∀ X : C,
      has_colimits_of_shape («expr ᵒᵖ» (J.cover X))
        D][∀ X : C, preserves_colimits_of_shape («expr ᵒᵖ» (J.cover X)) (forget D)][reflects_isomorphisms (forget D)]

/-- The sheafification functor, as a functor taking values in `Sheaf`. -/
@[simps obj map]
def presheaf_to_Sheaf : («expr ᵒᵖ» C ⥤ D) ⥤ Sheaf J D :=
  { obj := fun P => ⟨J.sheafify P, grothendieck_topology.plus.is_sheaf_plus_plus J P⟩,
    map := fun P Q η => (J.sheafification D).map η, map_id' := (J.sheafification D).map_id,
    map_comp' := fun P Q R => (J.sheafification D).map_comp }

/-- The sheafification functor is left adjoint to the forgetful functor. -/
def sheafification_adjunction : presheaf_to_Sheaf J D ⊣ Sheaf_to_presheaf J D :=
  adjunction.mk_of_hom_equiv
    { homEquiv :=
        fun P Q =>
          { toFun := fun e => J.to_sheafify P ≫ e, invFun := fun e => J.sheafify_lift e Q.2,
            left_inv := fun e => (J.sheafify_lift_unique _ _ _ rfl).symm,
            right_inv := fun e => J.to_sheafify_sheafify_lift _ _ },
      hom_equiv_naturality_left_symm' :=
        by 
          intro P Q R η γ 
          dsimp 
          symm 
          apply J.sheafify_lift_unique 
          erw [←category.assoc, ←(J.to_sheafification D).naturality, functor.id_map, category.assoc,
            J.to_sheafify_sheafify_lift],
      hom_equiv_naturality_right' :=
        fun P Q R η γ =>
          by 
            dsimp 
            rw [category.assoc]
            rfl }

variable{J D}

/-- A sheaf `P` is isomorphic to its own sheafification. -/
def sheafification_iso (P : Sheaf J D) : P ≅ (presheaf_to_Sheaf J D).obj ((Sheaf_to_presheaf J D).obj P) :=
  { Hom := (J.iso_sheafify P.2).Hom, inv := (J.iso_sheafify P.2).inv, hom_inv_id' := (J.iso_sheafify P.2).hom_inv_id,
    inv_hom_id' := (J.iso_sheafify P.2).inv_hom_id }

@[simp]
theorem sheafification_iso_hom (P : Sheaf J D) :
  (sheafification_iso P).Hom = J.to_sheafify ((Sheaf_to_presheaf _ _).obj P) :=
  rfl

@[simp]
theorem sheafification_iso_inv (P : Sheaf J D) : (sheafification_iso P).inv = J.sheafify_lift (𝟙 _) P.2 :=
  by 
    apply J.sheafify_lift_unique 
    erw [iso.comp_inv_eq, category.id_comp]
    rfl

instance is_iso_sheafification_adjunction_counit (P : Sheaf J D) :
  is_iso ((sheafification_adjunction J D).counit.app P) :=
  by 
    dsimp [sheafification_adjunction]
    erw [←sheafification_iso_inv]
    infer_instance

instance sheafification_reflective : is_iso (sheafification_adjunction J D).counit :=
  nat_iso.is_iso_of_is_iso_app _

end CategoryTheory

