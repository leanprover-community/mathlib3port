/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/
import Mathbin.Order.CompleteLattice
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Yoneda
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.Data.Set.Lattice

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

variable {X Y Z : C} (f : Y ⟶ X)

/-- A set of arrows all with codomain `X`. -/
def Presieve (X : C) :=
  ∀ ⦃Y⦄, Set (Y ⟶ X)deriving CompleteLattice

namespace Presieve

instance : Inhabited (Presieve X) :=
  ⟨⊤⟩

/-- Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to be
    the natural functor from the full subcategory of the over category `C/X` consisting
    of arrows in `S` to `C`. -/
abbrev diagram (S : Presieve X) : (FullSubcategory fun f : Over X => S f.Hom) ⥤ C :=
  fullSubcategoryInclusion _ ⋙ Over.forget X

/-- Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`. -/
abbrev cocone (S : Presieve X) : Cocone S.diagram :=
  (Over.forgetCocone X).whisker (fullSubcategoryInclusion _)

/-- Given a set of arrows `S` all with codomain `X`, and a set of arrows with codomain `Y` for each
`f : Y ⟶ X` in `S`, produce a set of arrows with codomain `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def Bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y) : Presieve X := fun Z h =>
  ∃ (Y : C)(g : Z ⟶ Y)(f : Y ⟶ X)(H : S f), R H g ∧ g ≫ f = h

@[simp]
theorem bind_comp {S : Presieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Presieve Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) :
    Bind S R (g ≫ f) :=
  ⟨_, _, _, h₁, h₂, rfl⟩

-- Note we can't make this into `has_singleton` because of the out-param.
/-- The singleton presieve.  -/
inductive Singleton : Presieve X
  | mk : singleton f

@[simp]
theorem singleton_eq_iff_domain (f g : Y ⟶ X) : Singleton f g ↔ f = g := by
  constructor
  · rintro ⟨a, rfl⟩
    rfl
    
  · rintro rfl
    apply singleton.mk
    

theorem singleton_self : Singleton f f :=
  singleton.mk

/-- Pullback a set of arrows with given codomain along a fixed map, by taking the pullback in the
category.
This is not the same as the arrow set of `sieve.pullback`, but there is a relation between them
in `pullback_arrows_comm`.
-/
inductive PullbackArrows [HasPullbacks C] (R : Presieve X) : Presieve Y
  | mk (Z : C) (h : Z ⟶ X) : R h → pullback_arrows (pullback.snd : pullback h f ⟶ Y)

theorem pullback_singleton [HasPullbacks C] (g : Z ⟶ X) :
    PullbackArrows f (Singleton g) = Singleton (pullback.snd : pullback g f ⟶ _) := by
  ext (W h)
  constructor
  · rintro ⟨W, _, _, _⟩
    exact singleton.mk
    
  · rintro ⟨_⟩
    exact pullback_arrows.mk Z g singleton.mk
    

/-- Construct the presieve given by the family of arrows indexed by `ι`. -/
inductive OfArrows {ι : Type _} (Y : ι → C) (f : ∀ i, Y i ⟶ X) : Presieve X
  | mk (i : ι) : of_arrows (f i)

theorem of_arrows_punit : (OfArrows _ fun _ : PUnit => f) = Singleton f := by
  ext (Y g)
  constructor
  · rintro ⟨_⟩
    apply singleton.mk
    
  · rintro ⟨_⟩
    exact of_arrows.mk PUnit.unit
    

theorem of_arrows_pullback [HasPullbacks C] {ι : Type _} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X) :
    (OfArrows (fun i => pullback (g i) f) fun i => pullback.snd) = PullbackArrows f (OfArrows Z g) := by
  ext (T h)
  constructor
  · rintro ⟨hk⟩
    exact pullback_arrows.mk _ _ (of_arrows.mk hk)
    
  · rintro ⟨W, k, hk₁⟩
    cases' hk₁ with i hi
    apply of_arrows.mk
    

theorem of_arrows_bind {ι : Type _} (Z : ι → C) (g : ∀ i : ι, Z i ⟶ X) (j : ∀ ⦃Y⦄ (f : Y ⟶ X), OfArrows Z g f → Type _)
    (W : ∀ ⦃Y⦄ (f : Y ⟶ X) (H), j f H → C) (k : ∀ ⦃Y⦄ (f : Y ⟶ X) (H i), W f H i ⟶ Y) :
    ((OfArrows Z g).bind fun Y f H => OfArrows (W f H) (k f H)) =
      OfArrows (fun i : Σi, j _ (OfArrows.mk i) => W (g i.1) _ i.2) fun ij => k (g ij.1) _ ij.2 ≫ g ij.1 :=
  by
  ext (Y f)
  constructor
  · rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩
    exact of_arrows.mk (Sigma.mk _ _)
    
  · rintro ⟨i⟩
    exact bind_comp _ (of_arrows.mk _) (of_arrows.mk _)
    

/-- Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preimage via `F`. -/
def FunctorPullback (R : Presieve (F.obj X)) : Presieve X := fun _ f => R (F.map f)

@[simp]
theorem functor_pullback_mem (R : Presieve (F.obj X)) {Y} (f : Y ⟶ X) : R.FunctorPullback F f ↔ R (F.map f) :=
  Iff.rfl

@[simp]
theorem functor_pullback_id (R : Presieve X) : R.FunctorPullback (𝟭 _) = R :=
  rfl

section FunctorPushforward

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/-- Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a sieve)
by taking the sieve generated by the image via `F`.
-/
def FunctorPushforward (S : Presieve X) : Presieve (F.obj X) := fun Y f =>
  ∃ (Z : C)(g : Z ⟶ X)(h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g

/-- An auxillary definition in order to fix the choice of the preimages between various definitions.
-/
@[nolint has_nonempty_instance]
structure FunctorPushforwardStructure (S : Presieve X) {Y} (f : Y ⟶ F.obj X) where
  preobj : C
  premap : preobj ⟶ X
  lift : Y ⟶ F.obj preobj
  cover : S premap
  fac : f = lift ≫ F.map premap

/-- The fixed choice of a preimage. -/
noncomputable def getFunctorPushforwardStructure {F : C ⥤ D} {S : Presieve X} {Y : D} {f : Y ⟶ F.obj X}
    (h : S.FunctorPushforward F f) : FunctorPushforwardStructure F S f := by
  choose Z f' g h₁ h using h
  exact ⟨Z, f', g, h₁, h⟩

theorem functor_pushforward_comp (R : Presieve X) :
    R.FunctorPushforward (F ⋙ G) = (R.FunctorPushforward F).FunctorPushforward G := by
  ext (x f)
  constructor
  · rintro ⟨X, f₁, g₁, h₁, rfl⟩
    exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩
    
  · rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩
    use ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩
    

theorem image_mem_functor_pushforward (R : Presieve X) {f : Y ⟶ X} (h : R f) : R.FunctorPushforward F (F.map f) :=
  ⟨Y, f, 𝟙 _, h, by simp⟩

end FunctorPushforward

end Presieve

/-- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X` which is closed under
left-composition.
-/
structure Sieve {C : Type u₁} [Category.{v₁} C] (X : C) where
  Arrows : Presieve X
  downward_closed' : ∀ {Y Z f} (hf : arrows f) (g : Z ⟶ Y), arrows (g ≫ f)

namespace Sieve

instance : CoeFun (Sieve X) fun _ => Presieve X :=
  ⟨Sieve.Arrows⟩

initialize_simps_projections Sieve (Arrows → apply)

variable {S R : Sieve X}

@[simp]
theorem downward_closed (S : Sieve X) {f : Y ⟶ X} (hf : S f) (g : Z ⟶ Y) : S (g ≫ f) :=
  S.downward_closed' hf g

theorem arrows_ext : ∀ {R S : Sieve X}, R.Arrows = S.Arrows → R = S
  | ⟨Ra, _⟩, ⟨Sa, _⟩, rfl => rfl

@[ext]
protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
  arrows_ext <| funext fun x => funext fun f => propext <| h f

protected theorem ext_iff {R S : Sieve X} : R = S ↔ ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f :=
  ⟨fun h Y f => h ▸ Iff.rfl, Sieve.ext⟩

open Lattice

/-- The supremum of a collection of sieves: the union of them all. -/
protected def sup (𝒮 : Set (Sieve X)) : Sieve X where
  Arrows Y := { f | ∃ S ∈ 𝒮, Sieve.Arrows S f }
  downward_closed' Y Z f := by
    rintro ⟨S, hS, hf⟩ g
    exact ⟨S, hS, S.downward_closed hf _⟩

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def inf (𝒮 : Set (Sieve X)) : Sieve X where
  Arrows Y := { f | ∀ S ∈ 𝒮, Sieve.Arrows S f }
  downward_closed' Y Z f hf g S H := S.downward_closed (hf S H) g

/-- The union of two sieves is a sieve. -/
protected def union (S R : Sieve X) : Sieve X where
  Arrows Y f := S f ∨ R f
  downward_closed' := by rintro Y Z f (h | h) g <;> simp [h]

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : Sieve X) : Sieve X where
  Arrows Y f := S f ∧ R f
  downward_closed' := by
    rintro Y Z f ⟨h₁, h₂⟩ g
    simp [h₁, h₂]

/-- Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional properties.
-/
instance : CompleteLattice (Sieve X) where
  le S R := ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f
  le_refl S f q := id
  le_trans S₁ S₂ S₃ S₁₂ S₂₃ Y f h := S₂₃ _ (S₁₂ _ h)
  le_antisymm S R p q := Sieve.ext fun Y f => ⟨p _, q _⟩
  top := { Arrows := fun _ => Set.Univ, downward_closed' := fun Y Z f g h => ⟨⟩ }
  bot := { Arrows := fun _ => ∅, downward_closed' := fun _ _ _ p _ => False.elim p }
  sup := Sieve.union
  inf := Sieve.inter
  sup := Sieve.sup
  inf := Sieve.inf
  le_Sup 𝒮 S hS Y f hf := ⟨S, hS, hf⟩
  Sup_le ℰ S hS Y f := by
    rintro ⟨R, hR, hf⟩
    apply hS R hR _ hf
  Inf_le _ _ hS _ _ h := h _ hS
  le_Inf _ _ hS _ _ hf _ hR := hS _ hR _ hf
  le_sup_left _ _ _ _ := Or.inl
  le_sup_right _ _ _ _ := Or.inr
  sup_le _ _ _ a b _ _ hf := hf.elim (a _) (b _)
  inf_le_left _ _ _ _ := And.left
  inf_le_right _ _ _ _ := And.right
  le_inf _ _ _ p q _ _ z := ⟨p _ z, q _ z⟩
  le_top _ _ _ _ := trivial
  bot_le _ _ _ := False.elim

/-- The maximal sieve always exists. -/
instance sieveInhabited : Inhabited (Sieve X) :=
  ⟨⊤⟩

@[simp]
theorem Inf_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) : inf Ss f ↔ ∀ (S : Sieve X) (H : S ∈ Ss), S f :=
  Iff.rfl

@[simp]
theorem Sup_apply {Ss : Set (Sieve X)} {Y} (f : Y ⟶ X) : sup Ss f ↔ ∃ (S : Sieve X)(H : S ∈ Ss), S f :=
  Iff.rfl

@[simp]
theorem inter_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊓ S) f ↔ R f ∧ S f :=
  Iff.rfl

@[simp]
theorem union_apply {R S : Sieve X} {Y} (f : Y ⟶ X) : (R ⊔ S) f ↔ R f ∨ S f :=
  Iff.rfl

@[simp]
theorem top_apply (f : Y ⟶ X) : (⊤ : Sieve X) f :=
  trivial

/-- Generate the smallest sieve containing the given set of arrows. -/
@[simps]
def generate (R : Presieve X) : Sieve X where
  Arrows Z f := ∃ (Y : _)(h : Z ⟶ Y)(g : Y ⟶ X), R g ∧ h ≫ g = f
  downward_closed' := by
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h
    exact ⟨_, h ≫ g, _, hf, by simp⟩

/-- Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
def bind (S : Presieve X) (R : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve X where
  Arrows := S.bind fun Y f h => R h
  downward_closed' := by
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩

open Order Lattice

theorem sets_iff_generate (R : Presieve X) (S : Sieve X) : generate R ≤ S ↔ R ≤ S :=
  ⟨fun H Y g hg => H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩, fun ss Y f => by
    rintro ⟨Z, f, g, hg, rfl⟩
    exact S.downward_closed (ss Z hg) f⟩

/-- Show that there is a galois insertion (generate, set_over). -/
def giGenerate : GaloisInsertion (generate : Presieve X → Sieve X) Arrows where
  gc := sets_iff_generate
  choice 𝒢 _ := generate 𝒢
  choice_eq _ _ := rfl
  le_l_u S Y f hf := ⟨_, 𝟙 _, _, hf, id_comp _⟩

theorem le_generate (R : Presieve X) : R ≤ generate R :=
  giGenerate.gc.le_u_l R

@[simp]
theorem generate_sieve (S : Sieve X) : generate S = S :=
  giGenerate.l_u_eq S

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
theorem id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
  ⟨fun h => top_unique fun Y f _ => by simpa using downward_closed _ h f, fun h => h.symm ▸ trivial⟩

/-- If an arrow set contains a split epi, it generates the maximal sieve. -/
theorem generate_of_contains_is_split_epi {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) : generate R = ⊤ := by
  rw [← id_mem_iff_eq_top]
  exact ⟨_, section_ f, f, hf, by simp⟩

@[simp]
theorem generate_of_singleton_is_split_epi (f : Y ⟶ X) [IsSplitEpi f] : generate (Presieve.Singleton f) = ⊤ :=
  generate_of_contains_is_split_epi f (Presieve.singleton_self _)

@[simp]
theorem generate_top : generate (⊤ : Presieve X) = ⊤ :=
  generate_of_contains_is_split_epi (𝟙 _) ⟨⟩

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
def pullback (h : Y ⟶ X) (S : Sieve X) : Sieve Y where
  Arrows Y sl := S (sl ≫ h)
  downward_closed' Z W f g h := by simp [g]

@[simp]
theorem pullback_id : S.pullback (𝟙 _) = S := by simp [sieve.ext_iff]

@[simp]
theorem pullback_top {f : Y ⟶ X} : (⊤ : Sieve X).pullback f = ⊤ :=
  top_unique fun _ g => id

theorem pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g := by
  simp [sieve.ext_iff]

@[simp]
theorem pullback_inter {f : Y ⟶ X} (S R : Sieve X) : (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f := by
  simp [sieve.ext_iff]

theorem pullback_eq_top_iff_mem (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ := by
  rw [← id_mem_iff_eq_top, pullback_apply, id_comp]

theorem pullback_eq_top_of_mem (S : Sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
  (pullback_eq_top_iff_mem f).1

/-- Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
def pushforward (f : Y ⟶ X) (R : Sieve Y) : Sieve X where
  Arrows Z gf := ∃ g, g ≫ f = gf ∧ R g
  downward_closed' := fun Z₁ Z₂ g ⟨j, k, z⟩ h => ⟨h ≫ j, by simp [k], by simp [z]⟩

theorem pushforward_apply_comp {R : Sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) : R.pushforward f (g ≫ f) :=
  ⟨g, rfl, hg⟩

theorem pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : Sieve Z) :
    R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
  Sieve.ext fun W h =>
    ⟨fun ⟨f₁, hq, hf₁⟩ => ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩, fun ⟨y, hy, z, hR, hz⟩ => ⟨z, by rwa [reassoc_of hR], hz⟩⟩

theorem galois_connection (f : Y ⟶ X) : GaloisConnection (Sieve.pushforward f) (Sieve.pullback f) := fun S R =>
  ⟨fun hR Z g hg => hR _ ⟨g, rfl, hg⟩, fun hS Z g ⟨h, hg, hh⟩ => hg ▸ hS h hh⟩

theorem pullback_monotone (f : Y ⟶ X) : Monotone (Sieve.pullback f) :=
  (galois_connection f).monotone_u

theorem pushforward_monotone (f : Y ⟶ X) : Monotone (Sieve.pushforward f) :=
  (galois_connection f).monotone_l

theorem le_pushforward_pullback (f : Y ⟶ X) (R : Sieve Y) : R ≤ (R.pushforward f).pullback f :=
  (galois_connection f).le_u_l _

theorem pullback_pushforward_le (f : Y ⟶ X) (R : Sieve X) : (R.pullback f).pushforward f ≤ R :=
  (galois_connection f).l_u_le _

theorem pushforward_union {f : Y ⟶ X} (S R : Sieve Y) : (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
  (galois_connection f).l_sup

theorem pushforward_le_bind_of_mem (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X) (h : S f) :
    (R h).pushforward f ≤ bind S R := by
  rintro Z _ ⟨g, rfl, hg⟩
  exact ⟨_, g, f, h, hg, rfl⟩

theorem le_pullback_bind (S : Presieve X) (R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) (f : Y ⟶ X) (h : S f) :
    R h ≤ (bind S R).pullback f := by
  rw [← GaloisConnection f]
  apply pushforward_le_bind_of_mem

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galoisCoinsertionOfMono (f : Y ⟶ X) [Mono f] : GaloisCoinsertion (Sieve.pushforward f) (Sieve.pullback f) := by
  apply (GaloisConnection f).toGaloisCoinsertion
  rintro S Z g ⟨g₁, hf, hg₁⟩
  rw [cancel_mono f] at hf
  rwa [← hf]

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galoisInsertionOfIsSplitEpi (f : Y ⟶ X) [IsSplitEpi f] : GaloisInsertion (Sieve.pushforward f) (Sieve.pullback f) :=
  by
  apply (GaloisConnection f).toGaloisInsertion
  intro S Z g hg
  refine' ⟨g ≫ section_ f, by simpa⟩

theorem pullback_arrows_comm [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (R : Presieve X) :
    Sieve.generate (R.PullbackArrows f) = (Sieve.generate R).pullback f := by
  ext (Z g)
  constructor
  · rintro ⟨_, h, k, hk, rfl⟩
    cases' hk with W g hg
    change (sieve.generate R).pullback f (h ≫ pullback.snd)
    rw [sieve.pullback_apply, assoc, ← pullback.condition, ← assoc]
    exact sieve.downward_closed _ (sieve.le_generate R W hg) (h ≫ pullback.fst)
    
  · rintro ⟨W, h, k, hk, comm⟩
    exact ⟨_, _, _, presieve.pullback_arrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩
    

section Functor

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/-- If `R` is a sieve, then the `category_theory.presieve.functor_pullback` of `R` is actually a sieve.
-/
@[simps]
def functorPullback (R : Sieve (F.obj X)) : Sieve X where
  Arrows := Presieve.FunctorPullback F R
  downward_closed' _ _ f hf g := by
    unfold presieve.functor_pullback
    rw [F.map_comp]
    exact R.downward_closed hf (F.map g)

@[simp]
theorem functor_pullback_arrows (R : Sieve (F.obj X)) : (R.FunctorPullback F).Arrows = R.Arrows.FunctorPullback F :=
  rfl

@[simp]
theorem functor_pullback_id (R : Sieve X) : R.FunctorPullback (𝟭 _) = R := by
  ext
  rfl

theorem functor_pullback_comp (R : Sieve ((F ⋙ G).obj X)) :
    R.FunctorPullback (F ⋙ G) = (R.FunctorPullback G).FunctorPullback F := by
  ext
  rfl

theorem functor_pushforward_extend_eq {R : Presieve X} :
    (generate R).Arrows.FunctorPushforward F = R.FunctorPushforward F := by
  ext (Y f)
  constructor
  · rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩
    
  · rintro ⟨X', g, f', h₁, h₂⟩
    exact ⟨X', g, f', le_generate R _ h₁, h₂⟩
    

/-- The sieve generated by the image of `R` under `F`. -/
@[simps]
def functorPushforward (R : Sieve X) : Sieve (F.obj X) where
  Arrows := R.Arrows.FunctorPushforward F
  downward_closed' Y Z f h g := by
    obtain ⟨X, α, β, hα, rfl⟩ := h
    exact ⟨X, α, g ≫ β, hα, by simp⟩

@[simp]
theorem functor_pushforward_id (R : Sieve X) : R.FunctorPushforward (𝟭 _) = R := by
  ext (X f)
  constructor
  · intro hf
    obtain ⟨X, g, h, hg, rfl⟩ := hf
    exact R.downward_closed hg h
    
  · intro hf
    exact ⟨X, f, 𝟙 _, hf, by simp⟩
    

theorem functor_pushforward_comp (R : Sieve X) :
    R.FunctorPushforward (F ⋙ G) = (R.FunctorPushforward F).FunctorPushforward G := by
  ext
  simpa [R.arrows.functor_pushforward_comp F G]

theorem functor_galois_connection (X : C) :
    GaloisConnection (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) (Sieve.functorPullback F) := by
  intro R S
  constructor
  · intro hle X f hf
    apply hle
    refine' ⟨X, f, 𝟙 _, hf, _⟩
    rw [id_comp]
    
  · rintro hle Y f ⟨X, g, h, hg, rfl⟩
    apply sieve.downward_closed S
    exact hle g hg
    

theorem functor_pullback_monotone (X : C) : Monotone (Sieve.functorPullback F : Sieve (F.obj X) → Sieve X) :=
  (functor_galois_connection F X).monotone_u

theorem functor_pushforward_monotone (X : C) : Monotone (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) :=
  (functor_galois_connection F X).monotone_l

theorem le_functor_pushforward_pullback (R : Sieve X) : R ≤ (R.FunctorPushforward F).FunctorPullback F :=
  (functor_galois_connection F X).le_u_l _

theorem functor_pullback_pushforward_le (R : Sieve (F.obj X)) : (R.FunctorPullback F).FunctorPushforward F ≤ R :=
  (functor_galois_connection F X).l_u_le _

theorem functor_pushforward_union (S R : Sieve X) :
    (S ⊔ R).FunctorPushforward F = S.FunctorPushforward F ⊔ R.FunctorPushforward F :=
  (functor_galois_connection F X).l_sup

theorem functor_pullback_union (S R : Sieve (F.obj X)) :
    (S ⊔ R).FunctorPullback F = S.FunctorPullback F ⊔ R.FunctorPullback F :=
  rfl

theorem functor_pullback_inter (S R : Sieve (F.obj X)) :
    (S ⊓ R).FunctorPullback F = S.FunctorPullback F ⊓ R.FunctorPullback F :=
  rfl

@[simp]
theorem functor_pushforward_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve X).FunctorPushforward F = ⊥ :=
  (functor_galois_connection F X).l_bot

@[simp]
theorem functor_pushforward_top (F : C ⥤ D) (X : C) : (⊤ : Sieve X).FunctorPushforward F = ⊤ := by
  refine' (generate_sieve _).symm.trans _
  apply generate_of_contains_is_split_epi (𝟙 (F.obj X))
  refine' ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩

@[simp]
theorem functor_pullback_bot (F : C ⥤ D) (X : C) : (⊥ : Sieve (F.obj X)).FunctorPullback F = ⊥ :=
  rfl

@[simp]
theorem functor_pullback_top (F : C ⥤ D) (X : C) : (⊤ : Sieve (F.obj X)).FunctorPullback F = ⊤ :=
  rfl

theorem image_mem_functor_pushforward (R : Sieve X) {V} {f : V ⟶ X} (h : R f) : R.FunctorPushforward F (F.map f) :=
  ⟨V, f, 𝟙 _, h, by simp⟩

/-- When `F` is essentially surjective and full, the galois connection is a galois insertion. -/
def essSurjFullFunctorGaloisInsertion [EssSurj F] [Full F] (X : C) :
    GaloisInsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) (Sieve.functorPullback F) := by
  apply (functor_galois_connection F X).toGaloisInsertion
  intro S Y f hf
  refine' ⟨_, F.preimage ((F.obj_obj_preimage_iso Y).Hom ≫ f), (F.obj_obj_preimage_iso Y).inv, _⟩
  simpa using S.downward_closed hf _

/-- When `F` is fully faithful, the galois connection is a galois coinsertion. -/
def fullyFaithfulFunctorGaloisCoinsertion [Full F] [Faithful F] (X : C) :
    GaloisCoinsertion (Sieve.functorPushforward F : Sieve X → Sieve (F.obj X)) (Sieve.functorPullback F) := by
  apply (functor_galois_connection F X).toGaloisCoinsertion
  rintro S Y f ⟨Z, g, h, h₁, h₂⟩
  rw [← F.image_preimage h, ← F.map_comp] at h₂
  rw [F.map_injective h₂]
  exact S.downward_closed h₁ _

end Functor

/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : Sieve X) : Cᵒᵖ ⥤ Type v₁ where
  obj Y := { g : Y.unop ⟶ X // S g }
  map Y Z f g := ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩

/-- If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def natTransOfLe {S T : Sieve X} (h : S ≤ T) : S.Functor ⟶ T.Functor where app Y f := ⟨f.1, h _ f.2⟩

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functorInclusion (S : Sieve X) : S.Functor ⟶ yoneda.obj X where app Y f := f.1

theorem nat_trans_of_le_comm {S T : Sieve X} (h : S ≤ T) : natTransOfLe h ≫ functorInclusion _ = functorInclusion _ :=
  rfl

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functor_inclusion_is_mono : Mono S.functorInclusion :=
  ⟨fun Z f g h => by
    ext (Y y)
    apply congr_fun (nat_trans.congr_app h Y) y⟩

-- TODO: Show that when `f` is mono, this is right inverse to `functor_inclusion` up to isomorphism.
/-- A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functor_inclusion`, shown in `sieve_of_functor_inclusion`.
-/
@[simps]
def sieveOfSubfunctor {R} (f : R ⟶ yoneda.obj X) : Sieve X where
  Arrows Y g := ∃ t, f.app (Opposite.op Y) t = g
  downward_closed' Y Z _ := by
    rintro ⟨t, rfl⟩ g
    refine' ⟨R.map g.op t, _⟩
    rw [functor_to_types.naturality _ _ f]
    simp

theorem sieve_of_subfunctor_functor_inclusion : sieveOfSubfunctor S.functorInclusion = S := by
  ext
  simp only [functor_inclusion_app, sieve_of_subfunctor_apply, Subtype.val_eq_coe]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact hf
    
  · intro hf
    exact ⟨⟨_, hf⟩, rfl⟩
    

instance functor_inclusion_top_is_iso : IsIso (⊤ : Sieve X).functorInclusion :=
  ⟨⟨{ app := fun Y a => ⟨a, ⟨⟩⟩ }, by tidy⟩⟩

end Sieve

end CategoryTheory

