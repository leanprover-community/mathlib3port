import Mathbin.Topology.Sheaves.SheafOfFunctions 
import Mathbin.Topology.Sheaves.Stalks 
import Mathbin.Topology.LocalHomeomorph 
import Mathbin.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `topology/sheaves/sheaf_of_functions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `Top.sheaf_to_Top`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalk_to_fiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/


universe v

noncomputable theory

variable {X : Top.{v}}

variable (T : X → Type v)

open TopologicalSpace

open Opposite

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.Types

namespace Top

/--
Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : prelocal_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate.
-/
structure prelocal_predicate where 
  pred : ∀ {U : opens X}, (∀ x : U, T x) → Prop 
  res : ∀ {U V : opens X} i : U ⟶ V f : ∀ x : V, T x h : pred f, pred fun x : U => f (i x)

variable (X)

/--
Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simps]
def continuous_prelocal (T : Top.{v}) : prelocal_predicate fun x : X => T :=
  { pred := fun U f => Continuous f,
    res := fun U V i f h => Continuous.comp h (opens.open_embedding_of_le i.le).Continuous }

/-- Satisfying the inhabited linter. -/
instance inhabited_prelocal_predicate (T : Top.{v}) : Inhabited (prelocal_predicate fun x : X => T) :=
  ⟨continuous_prelocal X T⟩

variable {X}

/--
Given a topological space `X : Top` and a type family `T : X → Type`,
a `P : local_predicate T` consists of:
* a family of predicates `P.pred`, one for each `U : opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate, and
* a proof that given some `f : Π x : U, T x`,
  if for every `x : U` we can find an open set `x ∈ V ≤ U`
  so that the restriction of `f` to `V` satisfies the predicate,
  then `f` itself satisfies the predicate.
-/
structure local_predicate extends prelocal_predicate T where 
  locality :
  ∀ {U : opens X} f : ∀ x : U, T x w : ∀ x : U, ∃ (V : opens X)(m : x.1 ∈ V)(i : V ⟶ U), pred fun x : V => f (i x : U),
    pred f

variable (X)

/--
Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuous_local (T : Top.{v}) : local_predicate fun x : X => T :=
  { continuous_prelocal X T with
    locality :=
      fun U f w =>
        by 
          apply continuous_iff_continuous_at.2
          intro x 
          specialize w x 
          rcases w with ⟨V, m, i, w⟩
          dsimp  at w 
          rw [continuous_iff_continuous_at] at w 
          specialize w ⟨x, m⟩
          simpa using (opens.open_embedding_of_le i.le).continuous_at_iff.1 w }

/-- Satisfying the inhabited linter. -/
instance inhabited_local_predicate (T : Top.{v}) : Inhabited (local_predicate _) :=
  ⟨continuous_local X T⟩

variable {X T}

/--
Given a `P : prelocal_predicate`, we can always construct a `local_predicate`
by asking that the condition from `P` holds locally near every point.
-/
def prelocal_predicate.sheafify {T : X → Type v} (P : prelocal_predicate T) : local_predicate T :=
  { pred := fun U f => ∀ x : U, ∃ (V : opens X)(m : x.1 ∈ V)(i : V ⟶ U), P.pred fun x : V => f (i x : U),
    res :=
      fun V U i f w x =>
        by 
          specialize w (i x)
          rcases w with ⟨V', m', i', p⟩
          refine' ⟨V⊓V', ⟨x.2, m'⟩, opens.inf_le_left _ _, _⟩
          convert P.res (opens.inf_le_right V V') _ p,
    locality :=
      fun U f w x =>
        by 
          specialize w x 
          rcases w with ⟨V, m, i, p⟩
          specialize p ⟨x.1, m⟩
          rcases p with ⟨V', m', i', p'⟩
          exact ⟨V', m', i' ≫ i, p'⟩ }

theorem prelocal_predicate.sheafify_of {T : X → Type v} {P : prelocal_predicate T} {U : opens X} {f : ∀ x : U, T x}
  (h : P.pred f) : P.sheafify.pred f :=
  fun x =>
    ⟨U, x.2, 𝟙 _,
      by 
        convert h 
        ext ⟨y, w⟩
        rfl⟩

/--
The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps]
def subpresheaf_to_Types (P : prelocal_predicate T) : presheaf (Type v) X :=
  { obj := fun U => { f : ∀ x : unop U, T x // P.pred f },
    map := fun U V i f => ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩ }

namespace SubpresheafToTypes

variable (P : prelocal_predicate T)

/--
The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def Subtype : subpresheaf_to_Types P ⟶ presheaf_to_Types X T :=
  { app := fun U f => f.1 }

open Top.Presheaf

-- error in Topology.Sheaves.LocalPredicate: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The functions satisfying a local predicate satisfy the sheaf condition.
-/ theorem is_sheaf (P : local_predicate T) : (subpresheaf_to_Types P.to_prelocal_predicate).is_sheaf :=
«expr $ »(presheaf.is_sheaf_of_is_sheaf_unique_gluing_types _, λ ι U sf sf_comp, begin
   let [ident sf'] [":", expr ∀ i : ι, (presheaf_to_Types X T).obj (op (U i))] [":=", expr λ i, (sf i).val],
   have [ident sf'_comp] [":", expr (presheaf_to_Types X T).is_compatible U sf'] [":=", expr λ
    i j, congr_arg subtype.val (sf_comp i j)],
   obtain ["⟨", ident gl, ",", ident gl_spec, ",", ident gl_uniq, "⟩", ":=", expr (sheaf_to_Types X T).exists_unique_gluing U sf' sf'_comp],
   refine [expr ⟨⟨gl, _⟩, _, _⟩],
   { apply [expr P.locality],
     rintros ["⟨", ident x, ",", ident mem, "⟩"],
     choose [] [ident i] [ident hi] ["using", expr opens.mem_supr.mp mem],
     use ["[", expr U i, ",", expr hi, ",", expr opens.le_supr U i, "]"],
     convert [] [expr (sf i).property] [],
     exact [expr gl_spec i] },
   { intro [ident i],
     ext1 [] [],
     exact [expr gl_spec i] },
   { intros [ident gl', ident hgl'],
     ext1 [] [],
     exact [expr gl_uniq gl'.1 (λ i, congr_arg subtype.val (hgl' i))] }
 end)

end SubpresheafToTypes

/--
The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheaf_to_Types (P : local_predicate T) : sheaf (Type v) X :=
  ⟨subpresheaf_to_Types P.to_prelocal_predicate, subpresheaf_to_Types.is_sheaf P⟩

/--
There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalk_to_fiber (P : local_predicate T) (x : X) : (subsheaf_to_Types P).1.stalk x ⟶ T x :=
  by 
    refine' colimit.desc _ { x := T x, ι := { app := fun U f => _, naturality' := _ } }
    ·
      exact f.1 ⟨x, (unop U).2⟩
    ·
      tidy

@[simp]
theorem stalk_to_fiber_germ (P : local_predicate T) (U : opens X) (x : U) f :
  stalk_to_fiber P x ((subsheaf_to_Types P).1.germ x f) = f.1 x :=
  by 
    dsimp [presheaf.germ, stalk_to_fiber]
    cases x 
    simp 
    rfl

/--
The `stalk_to_fiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it.
-/
theorem stalk_to_fiber_surjective (P : local_predicate T) (x : X)
  (w : ∀ t : T x, ∃ (U : open_nhds x)(f : ∀ y : U.1, T y)(h : P.pred f), f ⟨x, U.2⟩ = t) :
  Function.Surjective (stalk_to_fiber P x) :=
  fun t =>
    by 
      rcases w t with ⟨U, f, h, rfl⟩
      fsplit
      ·
        exact (subsheaf_to_Types P).1.germ ⟨x, U.2⟩ ⟨f, h⟩
      ·
        exact stalk_to_fiber_germ _ U.1 ⟨x, U.2⟩ ⟨f, h⟩

/--
The `stalk_to_fiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`.
-/
theorem stalk_to_fiber_injective (P : local_predicate T) (x : X)
  (w :
    ∀ U V : open_nhds x fU : ∀ y : U.1, T y hU : P.pred fU fV : ∀ y : V.1, T y hV : P.pred fV e :
      fU ⟨x, U.2⟩ = fV ⟨x, V.2⟩,
      ∃ (W : open_nhds x)(iU : W ⟶ U)(iV : W ⟶ V), ∀ w : W.1, fU (iU w : U.1) = fV (iV w : V.1)) :
  Function.Injective (stalk_to_fiber P x) :=
  fun tU tV h =>
    by 
      let Q :
        ∃ (W : «expr ᵒᵖ» (open_nhds x))(s : ∀ w : (unop W).1, T w)(hW : P.pred s),
          tU = (subsheaf_to_Types P).1.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ ∧
            tV = (subsheaf_to_Types P).1.germ ⟨x, (unop W).2⟩ ⟨s, hW⟩ :=
        _
      ·
        choose W s hW e using Q 
        exact e.1.trans e.2.symm 
      obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective' tU 
      obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective' tV
      ·
        dsimp 
        simp only [stalk_to_fiber, types.colimit.ι_desc_apply] at h 
        specialize w (unop U) (unop V) fU hU fV hV h 
        rcases w with ⟨W, iU, iV, w⟩
        refine' ⟨op W, fun w => fU (iU w : (unop U).1), P.res _ _ hU, _⟩
        rcases W with ⟨W, m⟩
        exact ⟨colimit_sound iU.op (Subtype.eq rfl), colimit_sound iV.op (Subtype.eq (funext w).symm)⟩

/--
Some repackaging:
the presheaf of functions satisfying `continuous_prelocal` is just the same thing as
the presheaf of continuous functions.
-/
def subpresheaf_continuous_prelocal_iso_presheaf_to_Top (T : Top.{v}) :
  subpresheaf_to_Types (continuous_prelocal X T) ≅ presheaf_to_Top X T :=
  nat_iso.of_components
    (fun X =>
      { Hom :=
          by 
            rintro ⟨f, c⟩
            exact ⟨f, c⟩,
        inv :=
          by 
            rintro ⟨f, c⟩
            exact ⟨f, c⟩,
        hom_inv_id' :=
          by 
            ext ⟨f, p⟩ x 
            rfl,
        inv_hom_id' :=
          by 
            ext ⟨f, p⟩ x 
            rfl })
    (by 
      tidy)

/--
The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheaf_to_Top (T : Top.{v}) : sheaf (Type v) X :=
  ⟨presheaf_to_Top X T,
    presheaf.is_sheaf_of_iso (subpresheaf_continuous_prelocal_iso_presheaf_to_Top T)
      (subpresheaf_to_Types.is_sheaf (continuous_local X T))⟩

end Top

