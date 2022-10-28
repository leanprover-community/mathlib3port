/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli, Junyan Xu
-/
import Mathbin.CategoryTheory.Groupoid.VertexGroup
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Data.Set.Lattice
import Mathbin.Combinatorics.Quiver.ConnectedComponent
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Order.GaloisConnection

/-!
# Subgroupoid

This file defines subgroupoids as `structure`s containing the subsets of arrows and their
stability under composition and inversion.
Also defined are

* containment of subgroupoids is a complete lattice;
* images and preimages of subgroupoids under a functor;
* the notion of normality of subgroupoids and its stability under intersection and preimage;
* compatibility of the above with `groupoid.vertex_group`.


## Main definitions

Given a type `C` with associated `groupoid C` instance.

* `subgroupoid C` is the type of subgroupoids of `C`
* `subgroupoid.is_normal` is the property that the subgroupoid is stable under conjugation
  by arbitrary arrows, _and_ that all identity arrows are contained in the subgroupoid.
* `subgroupoid.comap` is the "preimage" map of subgroupoids along a functor.
* `subgroupoid.map` is the "image" map of subgroupoids along a functor _injective on objects_.
* `subgroupoid.vertex_subgroup` is the subgroup of the `vertex group` at a given vertex `v`,
  assuming `v` is contained in the `subgroupoid` (meaning, by definition, that the arrow `𝟙 v`
  is contained in the subgroupoid).

## Implementation details

The structure of this file is copied from/inspired by `group_theory.subgroup.basic`
and `combinatorics.simple_graph.subgraph`.

## TODO

* Equivalent inductive characterization of generated (normal) subgroupoids.
* Characterization of normal subgroupoids as kernels.

## Tags

subgroupoid

-/


namespace CategoryTheory

open Set Groupoid

attribute [local protected] CategoryTheory.inv

universe u v

variable {C : Type u} [Groupoid C]

/-- A sugroupoid of `C` consists of a choice of arrows for each pair of vertices, closed
under composition and inverses.
-/
@[ext]
structure Subgroupoid (C : Type u) [Groupoid C] where
  Arrows : ∀ c d : C, Set (c ⟶ d)
  inv : ∀ {c d} {p : c ⟶ d} (hp : p ∈ arrows c d), inv p ∈ arrows d c
  mul : ∀ {c d e} {p} (hp : p ∈ arrows c d) {q} (hq : q ∈ arrows d e), p ≫ q ∈ arrows c e

attribute [protected] subgroupoid.inv subgroupoid.mul

namespace Subgroupoid

variable (S : Subgroupoid C)

theorem inv_mem_iff {c d : C} (f : c ⟶ d) : inv f ∈ S.Arrows d c ↔ f ∈ S.Arrows c d := by
  constructor
  · rintro h
    suffices inv (inv f) ∈ S.arrows c d by simpa only [inv_eq_inv, is_iso.inv_inv] using this
    · apply S.inv h
      
    
  · apply S.inv
    

theorem mul_mem_cancel_left {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hf : f ∈ S.Arrows c d) :
    f ≫ g ∈ S.Arrows c e ↔ g ∈ S.Arrows d e := by
  constructor
  · rintro h
    suffices inv f ≫ f ≫ g ∈ S.arrows d e by simpa only [inv_eq_inv, is_iso.inv_hom_id_assoc] using this
    · apply S.mul (S.inv hf) h
      
    
  · apply S.mul hf
    

theorem mul_mem_cancel_right {c d e : C} {f : c ⟶ d} {g : d ⟶ e} (hg : g ∈ S.Arrows d e) :
    f ≫ g ∈ S.Arrows c e ↔ f ∈ S.Arrows c d := by
  constructor
  · rintro h
    suffices (f ≫ g) ≫ inv g ∈ S.arrows c d by
      simpa only [inv_eq_inv, is_iso.hom_inv_id, category.comp_id, category.assoc] using this
    · apply S.mul h (S.inv hg)
      
    
  · exact fun hf => S.mul hf hg
    

/-- The vertices of `C` on which `S` has non-trivial isotropy -/
def Objs : Set C :=
  { c : C | (S.Arrows c c).Nonempty }

theorem mem_objs_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.Arrows c d) : c ∈ S.Objs :=
  ⟨f ≫ inv f, S.mul h (S.inv h)⟩

theorem mem_objs_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.Arrows c d) : d ∈ S.Objs :=
  ⟨inv f ≫ f, S.mul (S.inv h) h⟩

theorem id_mem_of_nonempty_isotropy (c : C) : c ∈ Objs S → 𝟙 c ∈ S.Arrows c c := by
  rintro ⟨γ, hγ⟩
  convert S.mul hγ (S.inv hγ)
  simp only [inv_eq_inv, is_iso.hom_inv_id]

theorem id_mem_of_src {c d : C} {f : c ⟶ d} (h : f ∈ S.Arrows c d) : 𝟙 c ∈ S.Arrows c c :=
  id_mem_of_nonempty_isotropy S c (mem_objs_of_src S h)

theorem id_mem_of_tgt {c d : C} {f : c ⟶ d} (h : f ∈ S.Arrows c d) : 𝟙 d ∈ S.Arrows d d :=
  id_mem_of_nonempty_isotropy S d (mem_objs_of_tgt S h)

/-- A subgroupoid seen as a quiver on vertex set `C` -/
def asWideQuiver : Quiver C :=
  ⟨fun c d => Subtype <| S.Arrows c d⟩

/-- The coercion of a subgroupoid as a groupoid -/
@[simps to_category_comp_coe, simps (config := lemmasOnly) inv_coe]
instance coe : Groupoid S.Objs where
  Hom a b := S.Arrows a.val b.val
  id a := ⟨𝟙 a.val, id_mem_of_nonempty_isotropy S a.val a.Prop⟩
  comp a b c p q := ⟨p.val ≫ q.val, S.mul p.Prop q.Prop⟩
  id_comp' := fun a b ⟨p, hp⟩ => by simp only [category.id_comp]
  comp_id' := fun a b ⟨p, hp⟩ => by simp only [category.comp_id]
  assoc' := fun a b c d ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩ => by simp only [category.assoc]
  inv a b p := ⟨inv p.val, S.inv p.Prop⟩
  inv_comp' := fun a b ⟨p, hp⟩ => by simp only [inv_comp]
  comp_inv' := fun a b ⟨p, hp⟩ => by simp only [comp_inv]

@[simp]
theorem coe_inv_coe' {c d : S.Objs} (p : c ⟶ d) : (CategoryTheory.inv p).val = CategoryTheory.inv p.val := by
  simp only [Subtype.val_eq_coe, ← inv_eq_inv, coe_inv_coe]

/-- The embedding of the coerced subgroupoid to its parent-/
def hom : S.Objs ⥤ C where
  obj c := c.val
  map c d f := f.val
  map_id' c := rfl
  map_comp' c d e f g := rfl

theorem hom.inj_on_objects : Function.Injective (hom S).obj := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  simp only [Subtype.mk_eq_mk]
  exact hcd

theorem hom.faithful : ∀ c d, Function.Injective fun f : c ⟶ d => (hom S).map f := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ ⟨f, hf⟩ ⟨g, hg⟩ hfg
  simp only [Subtype.mk_eq_mk]
  exact hfg

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
def vertexSubgroup {c : C} (hc : c ∈ S.Objs) : Subgroup (c ⟶ c) where
  Carrier := S.Arrows c c
  mul_mem' f g hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' f hf := S.inv hf

instance : SetLike (Subgroupoid C) (Σc d : C, c ⟶ d) where
  coe S := { F | F.2.2 ∈ S.Arrows F.1 F.2.1 }
  coe_injective' := fun ⟨S, _, _⟩ ⟨T, _, _⟩ h => by
    ext c d f
    apply Set.ext_iff.1 h ⟨c, d, f⟩

theorem mem_iff (S : Subgroupoid C) (F : Σc d, c ⟶ d) : F ∈ S ↔ F.2.2 ∈ S.Arrows F.1 F.2.1 :=
  Iff.rfl

theorem le_iff (S T : Subgroupoid C) : S ≤ T ↔ ∀ {c d}, S.Arrows c d ⊆ T.Arrows c d := by
  rw [SetLike.le_def, Sigma.forall]
  exact forall_congr' fun c => Sigma.forall

instance : HasTop (Subgroupoid C) :=
  ⟨{ Arrows := fun _ _ => Set.Univ,
      mul := by
        rintro
        trivial,
      inv := by
        rintro
        trivial }⟩

theorem mem_top {c d : C} (f : c ⟶ d) : f ∈ (⊤ : Subgroupoid C).Arrows c d :=
  trivial

theorem mem_top_objs (c : C) : c ∈ (⊤ : Subgroupoid C).Objs := by
  dsimp [HasTop.top, objs]
  simp only [univ_nonempty]

instance : HasBot (Subgroupoid C) :=
  ⟨{ Arrows := fun _ _ => ∅, mul := fun _ _ _ _ => False.elim, inv := fun _ _ _ => False.elim }⟩

instance : Inhabited (Subgroupoid C) :=
  ⟨⊤⟩

instance : HasInf (Subgroupoid C) :=
  ⟨fun S T =>
    { Arrows := fun c d => S.Arrows c d ∩ T.Arrows c d,
      inv := by
        rintro
        exact ⟨S.inv hp.1, T.inv hp.2⟩,
      mul := by
        rintro
        exact ⟨S.mul hp.1 hq.1, T.mul hp.2 hq.2⟩ }⟩

instance : HasInf (Subgroupoid C) :=
  ⟨fun s =>
    { Arrows := fun c d => ⋂ S ∈ s, Subgroupoid.Arrows S c d,
      inv := by
        intros
        rw [mem_Inter₂] at hp⊢
        exact fun S hS => S.inv (hp S hS),
      mul := by
        intros
        rw [mem_Inter₂] at hp hq⊢
        exact fun S hS => S.mul (hp S hS) (hq S hS) }⟩

instance : CompleteLattice (Subgroupoid C) :=
  { completeLatticeOfInf (Subgroupoid C)
      (by
        refine' fun s => ⟨fun S Ss F => _, fun T Tl F fT => _⟩ <;> simp only [Inf, mem_iff, mem_Inter]
        exacts[fun hp => hp S Ss, fun S Ss => Tl Ss fT]) with
    bot := ⊥, bot_le := fun S => empty_subset _, top := ⊤, le_top := fun S => subset_univ _, inf := (· ⊓ ·),
    le_inf := fun R S T RS RT _ pR => ⟨RS pR, RT pR⟩, inf_le_left := fun R S _ => And.left,
    inf_le_right := fun R S _ => And.right }

theorem le_objs {S T : Subgroupoid C} (h : S ≤ T) : S.Objs ⊆ T.Objs := fun s ⟨γ, hγ⟩ => ⟨γ, @h ⟨s, s, γ⟩ hγ⟩

/-- The functor associated to the embedding of subgroupoids -/
def inclusion {S T : Subgroupoid C} (h : S ≤ T) : S.Objs ⥤ T.Objs where
  obj s := ⟨s.val, le_objs h s.Prop⟩
  map s t f := ⟨f.val, @h ⟨s, t, f.val⟩ f.Prop⟩
  map_id' _ := rfl
  map_comp' _ _ _ _ _ := rfl

theorem inclusion_inj_on_objects {S T : Subgroupoid C} (h : S ≤ T) : Function.Injective (inclusion h).obj :=
  fun ⟨s, hs⟩ ⟨t, ht⟩ => by simpa only [inclusion, Subtype.mk_eq_mk] using id

theorem inclusion_faithful {S T : Subgroupoid C} (h : S ≤ T) (s t : S.Objs) :
    Function.Injective fun f : s ⟶ t => (inclusion h).map f := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
  dsimp only [inclusion]
  simpa only [Subtype.mk_eq_mk] using id

theorem inclusion_refl {S : Subgroupoid C} : inclusion (le_refl S) = 𝟭 S.Objs :=
  Functor.hext (fun ⟨s, hs⟩ => rfl) fun ⟨s, hs⟩ ⟨t, ht⟩ ⟨f, hf⟩ => heq_of_eq rfl

theorem inclusion_trans {R S T : Subgroupoid C} (k : R ≤ S) (h : S ≤ T) :
    inclusion (k.trans h) = inclusion k ⋙ inclusion h :=
  rfl

theorem inclusion_comp_embedding {S T : Subgroupoid C} (h : S ≤ T) : inclusion h ⋙ T.Hom = S.Hom :=
  rfl

/-- The family of arrows of the discrete groupoid -/
inductive Discrete.Arrows : ∀ c d : C, (c ⟶ d) → Prop
  | id (c : C) : discrete.arrows c c (𝟙 c)

/-- The only arrows of the discrete groupoid are the identity arrows. -/
def discrete : Subgroupoid C where
  Arrows := Discrete.Arrows
  inv := by
    rintro _ _ _ ⟨⟩
    simp only [inv_eq_inv, is_iso.inv_id]
    constructor
  mul := by
    rintro _ _ _ _ ⟨⟩ _ ⟨⟩
    rw [category.comp_id]
    constructor

theorem mem_discrete_iff {c d : C} (f : c ⟶ d) : f ∈ discrete.Arrows c d ↔ ∃ h : c = d, f = eqToHom h :=
  ⟨by
    rintro ⟨⟩
    exact ⟨rfl, rfl⟩, by
    rintro ⟨rfl, rfl⟩
    constructor⟩

/-- A subgroupoid is wide if its carrier set is all of `C`-/
structure IsWide : Prop where
  wide : ∀ c, 𝟙 c ∈ S.Arrows c c

theorem is_wide_iff_objs_eq_univ : S.IsWide ↔ S.Objs = Set.Univ := by
  constructor
  · rintro h
    ext
    constructor <;> simp only [top_eq_univ, mem_univ, imp_true_iff, forall_true_left]
    apply mem_objs_of_src S (h.wide x)
    
  · rintro h
    refine' ⟨fun c => _⟩
    obtain ⟨γ, γS⟩ := (le_of_eq h.symm : ⊤ ⊆ S.objs) (Set.mem_univ c)
    exact id_mem_of_src S γS
    

theorem IsWide.id_mem {S : Subgroupoid C} (Sw : S.IsWide) (c : C) : 𝟙 c ∈ S.Arrows c c :=
  Sw.wide c

theorem IsWide.eq_to_hom_mem {S : Subgroupoid C} (Sw : S.IsWide) {c d : C} (h : c = d) : eqToHom h ∈ S.Arrows c d := by
  cases h
  simp only [eq_to_hom_refl]
  apply Sw.id_mem c

/-- A subgroupoid is normal if it is wide and satisfies the expected stability under conjugacy. -/
structure IsNormal extends IsWide S : Prop where
  conj : ∀ {c d} (p : c ⟶ d) {γ : c ⟶ c} (hs : γ ∈ S.Arrows c c), inv p ≫ γ ≫ p ∈ S.Arrows d d

theorem IsNormal.conj' {S : Subgroupoid C} (Sn : IsNormal S) :
    ∀ {c d} (p : d ⟶ c) {γ : c ⟶ c} (hs : γ ∈ S.Arrows c c), p ≫ γ ≫ inv p ∈ S.Arrows d d := fun c d p γ hs => by
  convert Sn.conj (inv p) hs
  simp

theorem IsNormal.conjugation_bij (Sn : IsNormal S) {c d} (p : c ⟶ d) :
    Set.BijOn (fun γ : c ⟶ c => inv p ≫ γ ≫ p) (S.Arrows c c) (S.Arrows d d) := by
  refine' ⟨fun γ γS => Sn.conj p γS, fun γ₁ γ₁S γ₂ γ₂S h => _, fun δ δS => ⟨p ≫ δ ≫ inv p, Sn.conj' p δS, _⟩⟩
  · simpa only [inv_eq_inv, category.assoc, is_iso.hom_inv_id, category.comp_id, is_iso.hom_inv_id_assoc] using
      p ≫= h =≫ inv p
    
  · simp only [inv_eq_inv, category.assoc, is_iso.inv_hom_id, category.comp_id, is_iso.inv_hom_id_assoc]
    

theorem top_is_normal : IsNormal (⊤ : Subgroupoid C) :=
  { wide := fun c => trivial, conj := fun a b c d e => trivial }

theorem Inf_is_normal (s : Set <| Subgroupoid C) (sn : ∀ S ∈ s, IsNormal S) : IsNormal (inf s) :=
  { wide := by
      simp_rw [Inf, mem_Inter₂]
      exact fun c S Ss => (sn S Ss).wide c,
    conj := by
      simp_rw [Inf, mem_Inter₂]
      exact fun c d p γ hγ S Ss => (sn S Ss).conj p (hγ S Ss) }

theorem discrete_is_normal : (@discrete C _).IsNormal :=
  { wide := fun c => by constructor,
    conj := fun c d f γ hγ => by
      cases hγ
      simp only [inv_eq_inv, category.id_comp, is_iso.inv_hom_id]
      constructor }

theorem IsNormal.vertex_subgroup (Sn : IsNormal S) (c : C) (cS : c ∈ S.Objs) : (S.vertexSubgroup cS).Normal :=
  { conj_mem := fun x hx y => by
      rw [mul_assoc]
      exact Sn.conj' y hx }

section GeneratedSubgroupoid

-- TODO: proof that generated is just "words in X" and generated_normal is similarly
variable (X : ∀ c d : C, Set (c ⟶ d))

/-- The subgropoid generated by the set of arrows `X` -/
def generated : Subgroupoid C :=
  inf { S : Subgroupoid C | ∀ c d, X c d ⊆ S.Arrows c d }

theorem subset_generated (c d : C) : X c d ⊆ (generated X).Arrows c d := by
  dsimp only [generated, Inf]
  simp only [subset_Inter₂_iff]
  exact fun S hS f fS => hS _ _ fS

/-- The normal sugroupoid generated by the set of arrows `X` -/
def generatedNormal : Subgroupoid C :=
  inf { S : Subgroupoid C | (∀ c d, X c d ⊆ S.Arrows c d) ∧ S.IsNormal }

theorem generated_le_generated_normal : generated X ≤ generatedNormal X := by
  apply @Inf_le_Inf (subgroupoid C) _
  exact fun S ⟨h, _⟩ => h

theorem generated_normal_is_normal : (generatedNormal X).IsNormal :=
  Inf_is_normal _ fun S h => h.right

theorem IsNormal.generated_normal_le {S : Subgroupoid C} (Sn : S.IsNormal) :
    generatedNormal X ≤ S ↔ ∀ c d, X c d ⊆ S.Arrows c d := by
  constructor
  · rintro h c d
    let h' := generated_le_generated_normal X
    rw [le_iff] at h h'
    exact ((subset_generated X c d).trans (@h' c d)).trans (@h c d)
    
  · rintro h
    apply @Inf_le (subgroupoid C) _
    exact ⟨h, Sn⟩
    

end GeneratedSubgroupoid

section Hom

variable {D : Type _} [Groupoid D] (φ : C ⥤ D)

/-- A functor between groupoid defines a map of subgroupoids in the reverse direction
by taking preimages.
 -/
def comap (S : Subgroupoid D) : Subgroupoid C where
  Arrows c d := { f : c ⟶ d | φ.map f ∈ S.Arrows (φ.obj c) (φ.obj d) }
  inv c d p hp := by
    rw [mem_set_of, inv_eq_inv, φ.map_inv p, ← inv_eq_inv]
    exact S.inv hp
  mul := by
    rintro
    simp only [mem_set_of, functor.map_comp]
    apply S.mul <;> assumption

theorem comap_mono (S T : Subgroupoid D) : S ≤ T → comap φ S ≤ comap φ T := fun ST ⟨c, d, p⟩ => @ST ⟨_, _, _⟩

theorem is_normal_comap {S : Subgroupoid D} (Sn : IsNormal S) : IsNormal (comap φ S) :=
  { wide := fun c => by
      rw [comap, mem_set_of, Functor.map_id]
      apply Sn.wide,
    conj := fun c d f γ hγ => by
      simp_rw [inv_eq_inv f, comap, mem_set_of, functor.map_comp, functor.map_inv, ← inv_eq_inv]
      exact Sn.conj _ hγ }

@[simp]
theorem comap_comp {E : Type _} [Groupoid E] (ψ : D ⥤ E) : comap (φ ⋙ ψ) = comap φ ∘ comap ψ :=
  rfl

/-- The kernel of a functor between subgroupoid is the preimage. -/
def ker : Subgroupoid C :=
  comap φ discrete

theorem mem_ker_iff {c d : C} (f : c ⟶ d) : f ∈ (ker φ).Arrows c d ↔ ∃ h : φ.obj c = φ.obj d, φ.map f = eqToHom h :=
  mem_discrete_iff (φ.map f)

theorem ker_is_normal : (ker φ).IsNormal :=
  is_normal_comap φ discrete_is_normal

@[simp]
theorem ker_comp {E : Type _} [Groupoid E] (ψ : D ⥤ E) : ker (φ ⋙ ψ) = comap φ (ker ψ) :=
  rfl

/-- The family of arrows of the image of a subgroupoid under a functor injective on objects -/
inductive Map.Arrows (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : ∀ c d : D, (c ⟶ d) → Prop
  | im {c d : C} (f : c ⟶ d) (hf : f ∈ S.Arrows c d) : map.arrows (φ.obj c) (φ.obj d) (φ.map f)

theorem Map.arrows_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    Map.Arrows φ hφ S c d f ↔
      ∃ (a b : C)(g : a ⟶ b)(ha : φ.obj a = c)(hb : φ.obj b = d)(hg : g ∈ S.Arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨_, _, g, rfl, rfl, hg, eq_conj_eq_to_hom _⟩
    
  · rintro ⟨a, b, g, rfl, rfl, hg, rfl⟩
    rw [← eq_conj_eq_to_hom]
    constructor
    exact hg
    

/-- The "forward" image of a subgroupoid under a functor injective on objects -/
def map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : Subgroupoid D where
  Arrows := Map.Arrows φ hφ S
  inv := by
    rintro _ _ _ ⟨⟩
    rw [inv_eq_inv, ← functor.map_inv, ← inv_eq_inv]
    constructor
    apply S.inv
    assumption
  mul := by
    rintro _ _ _ _ ⟨f, hf⟩ q hq
    obtain ⟨c₃, c₄, g, he, rfl, hg, gq⟩ := (map.arrows_iff φ hφ S q).mp hq
    cases hφ he
    rw [gq, ← eq_conj_eq_to_hom, ← φ.map_comp]
    constructor
    exact S.mul hf hg

theorem mem_map_iff (hφ : Function.Injective φ.obj) (S : Subgroupoid C) {c d : D} (f : c ⟶ d) :
    f ∈ (map φ hφ S).Arrows c d ↔
      ∃ (a b : C)(g : a ⟶ b)(ha : φ.obj a = c)(hb : φ.obj b = d)(hg : g ∈ S.Arrows a b),
        f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  Map.arrows_iff φ hφ S f

theorem galois_connection_map_comap (hφ : Function.Injective φ.obj) : GaloisConnection (map φ hφ) (comap φ) := by
  rintro S T
  simp_rw [le_iff]
  constructor
  · exact fun h c d f fS => h (map.arrows.im f fS)
    
  · rintro h _ _ g ⟨a, gφS⟩
    exact h gφS
    

theorem map_mono (hφ : Function.Injective φ.obj) (S T : Subgroupoid C) : S ≤ T → map φ hφ S ≤ map φ hφ T := fun h =>
  (galois_connection_map_comap φ hφ).monotone_l h

theorem le_comap_map (hφ : Function.Injective φ.obj) (S : Subgroupoid C) : S ≤ comap φ (map φ hφ S) :=
  (galois_connection_map_comap φ hφ).le_u_l S

theorem map_comap_le (hφ : Function.Injective φ.obj) (T : Subgroupoid D) : map φ hφ (comap φ T) ≤ T :=
  (galois_connection_map_comap φ hφ).l_u_le T

theorem map_le_iff_le_comap (hφ : Function.Injective φ.obj) (S : Subgroupoid C) (T : Subgroupoid D) :
    map φ hφ S ≤ T ↔ S ≤ comap φ T :=
  (galois_connection_map_comap φ hφ).le_iff_le

theorem mem_map_objs_iff (hφ : Function.Injective φ.obj) (d : D) : d ∈ (map φ hφ S).Objs ↔ ∃ c ∈ S.Objs, φ.obj c = d :=
  by
  dsimp [objs, map]
  constructor
  · rintro ⟨f, hf⟩
    change map.arrows φ hφ S d d f at hf
    rw [map.arrows_iff] at hf
    obtain ⟨c, d, g, ec, ed, eg, gS, eg⟩ := hf
    exact ⟨c, ⟨mem_objs_of_src S eg, ec⟩⟩
    
  · rintro ⟨c, ⟨γ, γS⟩, rfl⟩
    exact ⟨φ.map γ, ⟨γ, γS⟩⟩
    

@[simp]
theorem map_objs_eq (hφ : Function.Injective φ.obj) : (map φ hφ S).Objs = φ.obj '' S.Objs := by
  ext
  convert mem_map_objs_iff S φ hφ x
  simp only [mem_image, exists_prop]

/-- The image of a functor injective on objects -/
def im (hφ : Function.Injective φ.obj) :=
  map φ hφ ⊤

theorem mem_im_iff (hφ : Function.Injective φ.obj) {c d : D} (f : c ⟶ d) :
    f ∈ (im φ hφ).Arrows c d ↔
      ∃ (a b : C)(g : a ⟶ b)(ha : φ.obj a = c)(hb : φ.obj b = d), f = eqToHom ha.symm ≫ φ.map g ≫ eqToHom hb :=
  by
  convert map.arrows_iff φ hφ ⊤ f
  simp only [HasTop.top, mem_univ, exists_true_left]

theorem mem_im_objs_iff (hφ : Function.Injective φ.obj) (d : D) : d ∈ (im φ hφ).Objs ↔ ∃ c : C, φ.obj c = d := by
  simp only [im, mem_map_objs_iff, mem_top_objs, exists_true_left]

theorem obj_surjective_of_im_eq_top (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) : Function.Surjective φ.obj :=
  by
  rintro d
  rw [← mem_im_objs_iff, hφ']
  apply mem_top_objs

theorem is_normal_map (hφ : Function.Injective φ.obj) (hφ' : im φ hφ = ⊤) (Sn : S.IsNormal) : (map φ hφ S).IsNormal :=
  { wide := fun d => by
      obtain ⟨c, rfl⟩ := obj_surjective_of_im_eq_top φ hφ hφ' d
      change map.arrows φ hφ S _ _ (𝟙 _)
      rw [← Functor.map_id]
      constructor
      exact Sn.wide c,
    conj := fun d d' g δ hδ => by
      rw [mem_map_iff] at hδ
      obtain ⟨c, c', γ, cd, cd', γS, hγ⟩ := hδ
      subst_vars
      cases hφ cd'
      have : d' ∈ (im φ hφ).Objs := by
        rw [hφ']
        apply mem_top_objs
      rw [mem_im_objs_iff] at this
      obtain ⟨c', rfl⟩ := this
      have : g ∈ (im φ hφ).Arrows (φ.obj c) (φ.obj c') := by
        rw [hφ']
        trivial
      rw [mem_im_iff] at this
      obtain ⟨b, b', f, hb, hb', _, hf⟩ := this
      subst_vars
      cases hφ hb
      cases hφ hb'
      change map.arrows φ hφ S (φ.obj c') (φ.obj c') _
      simp only [eq_to_hom_refl, category.comp_id, category.id_comp, inv_eq_inv]
      suffices map.arrows φ hφ S (φ.obj c') (φ.obj c') (φ.map <| inv f ≫ γ ≫ f) by
        simp only [inv_eq_inv, functor.map_comp, functor.map_inv] at this
        exact this
      · constructor
        apply Sn.conj f γS
         }

end Hom

end Subgroupoid

end CategoryTheory

