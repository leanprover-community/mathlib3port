import Mathbin.CategoryTheory.Sites.Canonical

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/


universe u

namespace CategoryTheory

open_locale CategoryTheory.Type

-- error in CategoryTheory.Sites.Types: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
def types_grothendieck_topology : grothendieck_topology (Type u) :=
{ sieves := λ α S, ∀ x : α, S (λ _ : punit, x),
  top_mem' := λ α x, trivial,
  pullback_stable' := λ α β S f hs x, hs (f x),
  transitive' := λ α S hs R hr x, hr (hs x) punit.star }

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simps]
def discrete_sieve (α : Type u) : sieve α :=
  { Arrows := fun β f => ∃ x, ∀ y, f y = x, downward_closed' := fun β γ f ⟨x, hx⟩ g => ⟨x, fun y => hx$ g y⟩ }

theorem discrete_sieve_mem (α : Type u) : discrete_sieve α ∈ types_grothendieck_topology α :=
  fun x => ⟨x, fun y => rfl⟩

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
def discrete_presieve (α : Type u) : presieve α :=
  fun β f => ∃ x : β, ∀ (y : β), y = x

theorem generate_discrete_presieve_mem (α : Type u) :
  sieve.generate (discrete_presieve α) ∈ types_grothendieck_topology α :=
  fun x => ⟨PUnit, id, fun _ => x, ⟨PUnit.unit, fun _ => Subsingleton.elimₓ _ _⟩, rfl⟩

open Presieve

theorem is_sheaf_yoneda' {α : Type u} : is_sheaf types_grothendieck_topology (yoneda.obj α) :=
  fun β S hs x hx =>
    ⟨fun y => x _ (hs y) PUnit.unit,
      fun γ f h =>
        funext$
          fun z =>
            have  := congr_funₓ (hx (𝟙 _) (fun _ => z) (hs$ f z) h rfl) PUnit.unit 
            by 
              convert this 
              exact rfl,
      fun f hf =>
        funext$
          fun y =>
            by 
              convert congr_funₓ (hf _ (hs y)) PUnit.unit⟩

/-- The yoneda functor that sends a type to a sheaf over the category of types -/
@[simps]
def yoneda' : Type u ⥤ SheafOfTypes types_grothendieck_topology :=
  { obj := fun α => ⟨yoneda.obj α, is_sheaf_yoneda'⟩, map := fun α β f => yoneda.map f }

@[simp]
theorem yoneda'_comp : yoneda'.{u} ⋙ induced_functor _ = yoneda :=
  rfl

open Opposite

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
def eval (P : «expr ᵒᵖ» (Type u) ⥤ Type u) (α : Type u) (s : P.obj (op α)) (x : α) : P.obj (op PUnit) :=
  P.map (↾fun _ => x).op s

/-- Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`. -/
noncomputable def types_glue (S : «expr ᵒᵖ» (Type u) ⥤ Type u) (hs : is_sheaf types_grothendieck_topology S)
  (α : Type u) (f : α → S.obj (op PUnit)) : S.obj (op α) :=
  (hs.is_sheaf_for _ _ (generate_discrete_presieve_mem α)).amalgamate
    (fun β g hg => S.map (↾fun x => PUnit.unit).op$ f$ g$ Classical.some hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
      (hs.is_sheaf_for _ _ (generate_discrete_presieve_mem δ)).IsSeparatedFor.ext$
        fun ε g ⟨x, hx⟩ =>
          have  : f₁ (Classical.some hf₁) = f₂ (Classical.some hf₂) :=
            Classical.some_spec hf₁ (g₁$ g x) ▸ Classical.some_spec hf₂ (g₂$ g x) ▸ congr_funₓ h _ 
          by 
            simpRw [←functor_to_types.map_comp_apply, this, ←op_comp]
            rfl

theorem eval_types_glue {S hs α} f : eval.{u} S α (types_glue S hs α f) = f :=
  funext$
    fun x =>
      (is_sheaf_for.valid_glue _ _ _$
            by 
              exact ⟨PUnit.unit, fun _ => Subsingleton.elimₓ _ _⟩).trans$
        by 
          convert functor_to_types.map_id_apply _ _ 
          rw [←op_id]
          congr

theorem types_glue_eval {S hs α} s : types_glue.{u} S hs α (eval S α s) = s :=
  (hs.is_sheaf_for _ _ (generate_discrete_presieve_mem α)).IsSeparatedFor.ext$
    fun β f hf =>
      (is_sheaf_for.valid_glue _ _ _ hf).trans$
        (functor_to_types.map_comp_apply _ _ _ _).symm.trans$
          by 
            rw [←op_comp]
            congr 2 
            exact funext fun x => congr_argₓ f (Classical.some_spec hf x).symm

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
@[simps]
noncomputable def eval_equiv (S : «expr ᵒᵖ» (Type u) ⥤ Type u) (hs : is_sheaf types_grothendieck_topology S)
  (α : Type u) : S.obj (op α) ≃ (α → S.obj (op PUnit)) :=
  { toFun := eval S α, invFun := types_glue S hs α, left_inv := types_glue_eval, right_inv := eval_types_glue }

theorem eval_map (S : «expr ᵒᵖ» (Type u) ⥤ Type u) α β (f : β ⟶ α) s x : eval S β (S.map f.op s) x = eval S α s (f x) :=
  by 
    simpRw [eval, ←functor_to_types.map_comp_apply, ←op_comp]
    rfl

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
noncomputable def equiv_yoneda (S : «expr ᵒᵖ» (Type u) ⥤ Type u) (hs : is_sheaf types_grothendieck_topology S) :
  S ≅ yoneda.obj (S.obj (op PUnit)) :=
  (nat_iso.of_components fun α => Equiv.toIso$ eval_equiv S hs$ unop α)$
    fun α β f => funext$ fun s => funext$ fun x => eval_map S (unop α) (unop β) f.unop _ _

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
noncomputable def equiv_yoneda' (S : SheafOfTypes types_grothendieck_topology) : S ≅ yoneda'.obj (S.1.obj (op PUnit)) :=
  { Hom := (equiv_yoneda S.1 S.2).Hom, inv := (equiv_yoneda S.1 S.2).inv,
    hom_inv_id' := (equiv_yoneda S.1 S.2).hom_inv_id, inv_hom_id' := (equiv_yoneda S.1 S.2).inv_hom_id }

-- error in CategoryTheory.Sites.Types: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem eval_app
(S₁ S₂ : SheafOfTypes.{u} types_grothendieck_topology)
(f : «expr ⟶ »(S₁, S₂))
(α : Type u)
(s : S₁.1.obj (op α))
(x : α) : «expr = »(eval S₂.1 α (f.app (op α) s) x, f.app (op punit) (eval S₁.1 α s x)) :=
(congr_fun (f.2 «expr↾ »(λ _ : punit, x).op) s).symm

/-- `yoneda'` induces an equivalence of category between `Type u` and
`Sheaf types_grothendieck_topology`. -/
@[simps]
noncomputable def type_equiv : Type u ≌ SheafOfTypes types_grothendieck_topology :=
  equivalence.mk yoneda' (induced_functor _ ⋙ (evaluation _ _).obj (op PUnit))
    (nat_iso.of_components
      (fun α =>
        { Hom := fun x _ => x, inv := fun f => f PUnit.unit, hom_inv_id' := funext$ fun x => rfl,
          inv_hom_id' := funext$ fun f => funext$ fun y => PUnit.casesOn y rfl })
      fun α β f => rfl)
    (iso.symm$
      nat_iso.of_components (fun S => equiv_yoneda' S)
        fun S₁ S₂ f =>
          nat_trans.ext _ _$ funext$ fun α => funext$ fun s => funext$ fun x => eval_app S₁ S₂ f (unop α) s x)

theorem subcanonical_types_grothendieck_topology : sheaf.subcanonical types_grothendieck_topology.{u} :=
  sheaf.subcanonical.of_yoneda_is_sheaf _ fun X => is_sheaf_yoneda'

theorem types_grothendieck_topology_eq_canonical :
  types_grothendieck_topology.{u} = sheaf.canonical_topology (Type u) :=
  le_antisymmₓ subcanonical_types_grothendieck_topology$
    Inf_le
      ⟨yoneda.obj (Ulift Bool), ⟨_, rfl⟩,
        grothendieck_topology.ext$
          funext$
            fun α =>
              Set.ext$
                fun S =>
                  ⟨fun hs x =>
                      Classical.by_contradiction$
                        fun hsx =>
                          have  :
                            (fun _ => Ulift.up tt : (yoneda.obj (Ulift Bool)).obj (op PUnit)) = fun _ => Ulift.up ff :=
                            (hs PUnit fun _ => x).IsSeparatedFor.ext$
                              fun β f hf => funext$ fun y => hsx.elim$ S.2 hf$ fun _ => y 
                          Bool.noConfusion$ Ulift.up.inj$ (congr_funₓ this PUnit.unit : _),
                    fun hs β f => is_sheaf_yoneda' _$ fun y => hs _⟩⟩

end CategoryTheory

