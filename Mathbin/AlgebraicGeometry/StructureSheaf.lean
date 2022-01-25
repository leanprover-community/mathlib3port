import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathbin.Algebra.Category.CommRing.Colimits
import Mathbin.Algebra.Category.CommRing.Limits
import Mathbin.Topology.Sheaves.LocalPredicate
import Mathbin.RingTheory.Localization
import Mathbin.RingTheory.Subring.Basic

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a ratio of
elements of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `topology.sheaves.sheaf_of_functions`,
where we show that dependent functions into any type family form a sheaf,
and also `topology.sheaves.local_predicate`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

We also set up the ring structure, obtaining
`structure_sheaf R : sheaf CommRing (Top.of (prime_spectrum R))`.

We then construct two basic isomorphisms, relating the structure sheaf to the underlying ring `R`.
First, `structure_sheaf.stalk_iso` gives an isomorphism between the stalk of the structure sheaf
at a point `p` and the localization of `R` at the prime ideal `p`. Second,
`structure_sheaf.basic_open_iso` gives an isomorphism between the structure sheaf on `basic_open f`
and the localization of `R` at the submonoid of powers of `f`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


universe u

noncomputable section

variable (R : Type u) [CommRingₓ R]

open Top

open TopologicalSpace

open CategoryTheory

open Opposite

namespace AlgebraicGeometry

/-- The prime spectrum, just as a topological space.
-/
def prime_spectrum.Top : Top :=
  Top.of (PrimeSpectrum R)

namespace StructureSheaf

/-- The type family over `prime_spectrum R` consisting of the localization over each point.
-/
def localizations (P : prime_spectrum.Top R) : Type u :=
  Localization.AtPrime P.as_ideal deriving CommRingₓ, LocalRing

instance (P : prime_spectrum.Top R) : Inhabited (localizations R P) :=
  ⟨1⟩

instance (U : opens (prime_spectrum.Top R)) (x : U) : Algebra R (localizations R x) :=
  Localization.algebra

instance (U : opens (prime_spectrum.Top R)) (x : U) :
    IsLocalization.AtPrime (localizations R x) (x : prime_spectrum.Top R).asIdeal :=
  Localization.is_localization

variable {R}

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (prime_spectrum.Top R)} (f : ∀ x : U, localizations R x) : Prop :=
  ∃ r s : R, ∀ x : U, ¬s ∈ x.1.asIdeal ∧ f x * algebraMap _ _ s = algebraMap _ _ r

theorem is_fraction.eq_mk' {U : opens (prime_spectrum.Top R)} {f : ∀ x : U, localizations R x} (hf : is_fraction f) :
    ∃ r s : R,
      ∀ x : U,
        ∃ hs : s ∉ x.1.asIdeal,
          f x =
            IsLocalization.mk' (Localization.AtPrime _) r (⟨s, hs⟩ : (x : prime_spectrum.Top R).asIdeal.primeCompl) :=
  by
  rcases hf with ⟨r, s, h⟩
  refine' ⟨r, s, fun x => ⟨(h x).1, (is_localization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩
  exact (h x).2.symm

variable (R)

/-- The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (localizations R) where
  pred := fun U f => is_fraction f
  res := by
    rintro V U i f ⟨r, s, w⟩
    exact ⟨r, s, fun x => w (i x)⟩

/-- We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, localizations x`.
-/
def is_locally_fraction : local_predicate (localizations R) :=
  (is_fraction_prelocal R).sheafify

@[simp]
theorem is_locally_fraction_pred {U : opens (prime_spectrum.Top R)} (f : ∀ x : U, localizations R x) :
    (is_locally_fraction R).pred f =
      ∀ x : U,
        ∃ (V : _)(m : x.1 ∈ V)(i : V ⟶ U),
          ∃ r s : R, ∀ y : V, ¬s ∈ y.1.asIdeal ∧ f (i y : U) * algebraMap _ _ s = algebraMap _ _ r :=
  rfl

/-- The functions satisfying `is_locally_fraction` form a subring.
-/
def sections_subring (U : opens (prime_spectrum.Top R)ᵒᵖ) : Subring (∀ x : unop U, localizations R x) where
  Carrier := { f | (is_locally_fraction R).pred f }
  zero_mem' := by
    refine' fun x => ⟨unop U, x.2, 𝟙 _, 0, 1, fun y => ⟨_, _⟩⟩
    · rw [← Ideal.ne_top_iff_one]
      exact y.1.IsPrime.1
      
    · simp
      
  one_mem' := by
    refine' fun x => ⟨unop U, x.2, 𝟙 _, 1, 1, fun y => ⟨_, _⟩⟩
    · rw [← Ideal.ne_top_iff_one]
      exact y.1.IsPrime.1
      
    · simp
      
  add_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine' ⟨Va⊓Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * sb + rb * sa, sa * sb, _⟩
    intro y
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H
      cases y.1.IsPrime.mem_or_mem H <;> contradiction
      
    · simp only [add_mulₓ, RingHom.map_add, Pi.add_apply, RingHom.map_mul]
      erw [← wa, ← wb]
      simp only [mul_assoc]
      congr 2
      rw [mul_comm]
      rfl
      
  neg_mem' := by
    intro a ha x
    rcases ha x with ⟨V, m, i, r, s, w⟩
    refine' ⟨V, m, i, -r, s, _⟩
    intro y
    rcases w y with ⟨nm, w⟩
    fconstructor
    · exact nm
      
    · simp only [RingHom.map_neg, Pi.neg_apply]
      erw [← w]
      simp only [neg_mul_eq_neg_mul_symm]
      
  mul_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine' ⟨Va⊓Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb, _⟩
    intro y
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H
      cases y.1.IsPrime.mem_or_mem H <;> contradiction
      
    · simp only [Pi.mul_apply, RingHom.map_mul]
      erw [← wa, ← wb]
      simp only [mul_left_commₓ, mul_assoc, mul_comm]
      rfl
      

end StructureSheaf

open StructureSheaf

/-- The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf (Type u) (prime_spectrum.Top R) :=
  subsheaf_to_Types (is_locally_fraction R)

instance comm_ring_structure_sheaf_in_Type_obj (U : opens (prime_spectrum.Top R)ᵒᵖ) :
    CommRingₓ ((structure_sheaf_in_Type R).1.obj U) :=
  (sections_subring R U).toCommRing

open _Root_.PrimeSpectrum

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRingₓₓ (prime_spectrum.Top R) where
  obj := fun U => CommRingₓₓ.of ((structure_sheaf_in_Type R).1.obj U)
  map := fun U V i =>
    { toFun := (structure_sheaf_in_Type R).1.map i, map_zero' := rfl, map_add' := fun x y => rfl, map_one' := rfl,
      map_mul' := fun x y => rfl }

/-- Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
    structure_presheaf_in_CommRing R ⋙ forget CommRingₓₓ ≅ (structure_sheaf_in_Type R).1 :=
  nat_iso.of_components (fun U => iso.refl _)
    (by
      tidy)

open Top.Presheaf

/-- The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def structure_sheaf : sheaf CommRingₓₓ (prime_spectrum.Top R) :=
  ⟨structure_presheaf_in_CommRing R,
    (is_sheaf_iff_is_sheaf_comp _ _).mpr
      (is_sheaf_of_iso (structure_presheaf_comp_forget R).symm (structure_sheaf_in_Type R).property)⟩

namespace StructureSheaf

@[simp]
theorem res_apply (U V : opens (prime_spectrum.Top R)) (i : V ⟶ U) (s : (structure_sheaf R).1.obj (op U)) (x : V) :
    ((structure_sheaf R).1.map i.op s).1 x = (s.1 (i x) : _) :=
  rfl

/-- The section of `structure_sheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
def const (f g : R) (U : opens (prime_spectrum.Top R))
    (hu : ∀, ∀ x ∈ U, ∀, g ∈ (x : prime_spectrum.Top R).asIdeal.primeCompl) : (structure_sheaf R).1.obj (op U) :=
  ⟨fun x => IsLocalization.mk' _ f ⟨g, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y y.2, IsLocalization.mk'_spec _ _ _⟩⟩⟩

@[simp]
theorem const_apply (f g : R) (U : opens (prime_spectrum.Top R))
    (hu : ∀, ∀ x ∈ U, ∀, g ∈ (x : prime_spectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hu x x.2⟩ :=
  rfl

theorem const_apply' (f g : R) (U : opens (prime_spectrum.Top R))
    (hu : ∀, ∀ x ∈ U, ∀, g ∈ (x : prime_spectrum.Top R).asIdeal.primeCompl) (x : U)
    (hx : g ∈ (as_ideal (x : prime_spectrum.Top R)).primeCompl) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hx⟩ :=
  rfl

theorem exists_const U (s : (structure_sheaf R).1.obj (op U)) (x : prime_spectrum.Top R) (hx : x ∈ U) :
    ∃ (V : opens (prime_spectrum.Top R))(hxV : x ∈ V)(i : V ⟶ U)(f g : R)(hg : _),
      const R f g V hg = (structure_sheaf R).1.map i.op s :=
  let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  ⟨V, hxV, iVU, f, g, fun y hyV => (hfg ⟨y, hyV⟩).1,
    Subtype.eq $ funext $ fun y => IsLocalization.mk'_eq_iff_eq_mul.2 $ Eq.symm $ (hfg y).2⟩

@[simp]
theorem res_const (f g : R) U hu V hv i : (structure_sheaf R).1.map i (const R f g U hu) = const R f g V hv :=
  rfl

theorem res_const' (f g : R) V hv :
    (structure_sheaf R).1.map (hom_of_le hv).op (const R f g (basic_open g) fun _ => id) = const R f g V hv :=
  rfl

theorem const_zero (f : R) U hu : const R 0 f U hu = 0 :=
  Subtype.eq $
    funext $ fun x =>
      IsLocalization.mk'_eq_iff_eq_mul.2 $ by
        erw [RingHom.map_zero, Subtype.val_eq_coe, Subring.coe_zero, Pi.zero_apply, zero_mul]

theorem const_self (f : R) U hu : const R f f U hu = 1 :=
  Subtype.eq $ funext $ fun x => IsLocalization.mk'_self _ _

theorem const_one U : (const R 1 1 U fun p _ => Submonoid.one_mem _) = 1 :=
  const_self R 1 U _

theorem const_add (f₁ f₂ g₁ g₂ : R) U hu₁ hu₂ :
    const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
      const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U fun x hx => Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq $
    funext $ fun x =>
      Eq.symm $ by
        convert IsLocalization.mk'_add f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

theorem const_mul (f₁ f₂ g₁ g₂ : R) U hu₁ hu₂ :
    const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
      const R (f₁ * f₂) (g₁ * g₂) U fun x hx => Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq $
    funext $ fun x =>
      Eq.symm $ by
        convert IsLocalization.mk'_mul _ f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

theorem const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) : const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
  Subtype.eq $ funext $ fun x => IsLocalization.mk'_eq_of_eq h.symm

theorem const_congr {f₁ f₂ g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const R f₁ g₁ U hu = const R f₂ g₂ U (hg ▸ hu) := by
  substs hf hg

theorem const_mul_rev (f g : R) U hu₁ hu₂ : const R f g U hu₁ * const R g f U hu₂ = 1 := by
  rw [const_mul, const_congr R rfl (mul_comm g f), const_self]

theorem const_mul_cancel (f g₁ g₂ : R) U hu₁ hu₂ : const R f g₁ U hu₁ * const R g₁ g₂ U hu₂ = const R f g₂ U hu₂ := by
  rw [const_mul, const_ext]
  rw [mul_assoc]

theorem const_mul_cancel' (f g₁ g₂ : R) U hu₁ hu₂ : const R g₁ g₂ U hu₂ * const R f g₁ U hu₁ = const R f g₂ U hu₂ := by
  rw [mul_comm, const_mul_cancel]

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
def to_open (U : opens (prime_spectrum.Top R)) : CommRingₓₓ.of R ⟶ (structure_sheaf R).1.obj (op U) where
  toFun := fun f =>
    ⟨fun x => algebraMap R _ f, fun x =>
      ⟨U, x.2, 𝟙 _, f, 1, fun y =>
        ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by
          rw [RingHom.map_one, mul_oneₓ]
          rfl⟩⟩⟩
  map_one' := Subtype.eq $ funext $ fun x => RingHom.map_one _
  map_mul' := fun f g => Subtype.eq $ funext $ fun x => RingHom.map_mul _ _ _
  map_zero' := Subtype.eq $ funext $ fun x => RingHom.map_zero _
  map_add' := fun f g => Subtype.eq $ funext $ fun x => RingHom.map_add _ _ _

@[simp]
theorem to_open_res (U V : opens (prime_spectrum.Top R)) (i : V ⟶ U) :
    to_open R U ≫ (structure_sheaf R).1.map i.op = to_open R V :=
  rfl

@[simp]
theorem to_open_apply (U : opens (prime_spectrum.Top R)) (f : R) (x : U) : (to_open R U f).1 x = algebraMap _ _ f :=
  rfl

theorem to_open_eq_const (U : opens (prime_spectrum.Top R)) (f : R) :
    to_open R U f = const R f 1 U fun x _ => (Ideal.ne_top_iff_one _).1 x.2.1 :=
  Subtype.eq $ funext $ fun x => Eq.symm $ IsLocalization.mk'_one _ f

/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structure_sheaf R` at `x`. -/
def to_stalk (x : prime_spectrum.Top R) : CommRingₓₓ.of R ⟶ (structure_sheaf R).1.stalk x :=
  (to_open R ⊤ ≫ (structure_sheaf R).1.germ ⟨x, ⟨⟩⟩ : _)

@[simp]
theorem to_open_germ (U : opens (prime_spectrum.Top R)) (x : U) :
    to_open R U ≫ (structure_sheaf R).1.germ x = to_stalk R x := by
  rw [← to_open_res R ⊤ U (hom_of_le le_top : U ⟶ ⊤), category.assoc, presheaf.germ_res]
  rfl

@[simp]
theorem germ_to_open (U : opens (prime_spectrum.Top R)) (x : U) (f : R) :
    (structure_sheaf R).1.germ x (to_open R U f) = to_stalk R x f := by
  rw [← to_open_germ]
  rfl

theorem germ_to_top (x : prime_spectrum.Top R) (f : R) :
    (structure_sheaf R).1.germ (⟨x, trivialₓ⟩ : (⊤ : opens (prime_spectrum.Top R))) (to_open R ⊤ f) = to_stalk R x f :=
  rfl

theorem is_unit_to_basic_open_self (f : R) : IsUnit (to_open R (basic_open f) f) :=
  is_unit_of_mul_eq_one _ (const R 1 f (basic_open f) fun _ => id) $ by
    rw [to_open_eq_const, const_mul_rev]

theorem is_unit_to_stalk (x : prime_spectrum.Top R) (f : x.as_ideal.prime_compl) : IsUnit (to_stalk R x (f : R)) := by
  erw [← germ_to_open R (basic_open (f : R)) ⟨x, f.2⟩ (f : R)]
  exact RingHom.is_unit_map _ (is_unit_to_basic_open_self R f)

/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localization_to_stalk (x : prime_spectrum.Top R) :
    CommRingₓₓ.of (Localization.AtPrime x.as_ideal) ⟶ (structure_sheaf R).1.stalk x :=
  show Localization.AtPrime x.as_ideal →+* _ from IsLocalization.lift (is_unit_to_stalk R x)

@[simp]
theorem localization_to_stalk_of (x : prime_spectrum.Top R) (f : R) :
    localization_to_stalk R x (algebraMap _ (Localization _) f) = to_stalk R x f :=
  IsLocalization.lift_eq _ f

@[simp]
theorem localization_to_stalk_mk' (x : prime_spectrum.Top R) (f : R) (s : (as_ideal x).primeCompl) :
    localization_to_stalk R x (IsLocalization.mk' _ f s : Localization _) =
      (structure_sheaf R).1.germ (⟨x, s.2⟩ : basic_open (s : R)) (const R f s (basic_open s) fun _ => id) :=
  (IsLocalization.lift_mk'_spec _ _ _ _).2 $ by
    erw [← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← RingHom.map_mul,
      to_open_eq_const, to_open_eq_const, const_mul_cancel']

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def open_to_localization (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R) (hx : x ∈ U) :
    (structure_sheaf R).1.obj (op U) ⟶ CommRingₓₓ.of (Localization.AtPrime x.as_ideal) where
  toFun := fun s => (s.1 ⟨x, hx⟩ : _)
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp]
theorem coe_open_to_localization (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R) (hx : x ∈ U) :
    (open_to_localization R U x hx : (structure_sheaf R).1.obj (op U) → Localization.AtPrime x.as_ideal) = fun s =>
      (s.1 ⟨x, hx⟩ : _) :=
  rfl

theorem open_to_localization_apply (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R) (hx : x ∈ U)
    (s : (structure_sheaf R).1.obj (op U)) : open_to_localization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
  rfl

/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `open_to_localization` maps. -/
def stalk_to_fiber_ring_hom (x : prime_spectrum.Top R) :
    (structure_sheaf R).1.stalk x ⟶ CommRingₓₓ.of (Localization.AtPrime x.as_ideal) :=
  limits.colimit.desc ((open_nhds.inclusion x).op ⋙ (structure_sheaf R).1)
    { x := _, ι := { app := fun U => open_to_localization R ((open_nhds.inclusion _).obj (unop U)) x (unop U).2 } }

@[simp]
theorem germ_comp_stalk_to_fiber_ring_hom (U : opens (prime_spectrum.Top R)) (x : U) :
    (structure_sheaf R).1.germ x ≫ stalk_to_fiber_ring_hom R x = open_to_localization R U x x.2 :=
  limits.colimit.ι_desc _ _

@[simp]
theorem stalk_to_fiber_ring_hom_germ' (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R) (hx : x ∈ U)
    (s : (structure_sheaf R).1.obj (op U)) :
    stalk_to_fiber_ring_hom R x ((structure_sheaf R).1.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
  RingHom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom R U ⟨x, hx⟩ : _) s

@[simp]
theorem stalk_to_fiber_ring_hom_germ (U : opens (prime_spectrum.Top R)) (x : U) (s : (structure_sheaf R).1.obj (op U)) :
    stalk_to_fiber_ring_hom R x ((structure_sheaf R).1.germ x s) = s.1 x := by
  cases x
  exact stalk_to_fiber_ring_hom_germ' R U _ _ _

@[simp]
theorem to_stalk_comp_stalk_to_fiber_ring_hom (x : prime_spectrum.Top R) :
    to_stalk R x ≫ stalk_to_fiber_ring_hom R x = (algebraMap _ _ : R →+* Localization _) := by
  erw [to_stalk, category.assoc, germ_comp_stalk_to_fiber_ring_hom]
  rfl

@[simp]
theorem stalk_to_fiber_ring_hom_to_stalk (x : prime_spectrum.Top R) (f : R) :
    stalk_to_fiber_ring_hom R x (to_stalk R x f) = algebraMap _ (Localization _) f :=
  RingHom.ext_iff.1 (to_stalk_comp_stalk_to_fiber_ring_hom R x) _

/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps]
def stalk_iso (x : prime_spectrum.Top R) :
    (structure_sheaf R).1.stalk x ≅ CommRingₓₓ.of (Localization.AtPrime x.as_ideal) where
  hom := stalk_to_fiber_ring_hom R x
  inv := localization_to_stalk R x
  hom_inv_id' :=
    (structure_sheaf R).1.stalk_hom_ext $ fun U hxU => by
      ext s
      simp only [comp_apply]
      rw [id_apply, stalk_to_fiber_ring_hom_germ']
      obtain ⟨V, hxV, iVU, f, g, hg, hs⟩ := exists_const _ _ s x hxU
      erw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localization_to_stalk_mk']
      refine' (structure_sheaf R).1.germ_ext V hxV (hom_of_le hg) iVU _
      erw [← hs, res_const']
  inv_hom_id' :=
    @IsLocalization.ring_hom_ext R _ x.as_ideal.prime_compl (Localization.AtPrime x.as_ideal) _ _
        (Localization.AtPrime x.as_ideal) _ _ (RingHom.comp (stalk_to_fiber_ring_hom R x) (localization_to_stalk R x))
        (RingHom.id (Localization.AtPrime _)) $
      by
      ext f
      simp only [RingHom.comp_apply, RingHom.id_apply, localization_to_stalk_of, stalk_to_fiber_ring_hom_to_stalk]

instance (x : PrimeSpectrum R) : is_iso (stalk_to_fiber_ring_hom R x) :=
  is_iso.of_iso (stalk_iso R x)

instance (x : PrimeSpectrum R) : is_iso (localization_to_stalk R x) :=
  is_iso.of_iso (stalk_iso R x).symm

@[simp, reassoc]
theorem stalk_to_fiber_ring_hom_localization_to_stalk (x : prime_spectrum.Top R) :
    stalk_to_fiber_ring_hom R x ≫ localization_to_stalk R x = 𝟙 _ :=
  (stalk_iso R x).hom_inv_id

@[simp, reassoc]
theorem localization_to_stalk_stalk_to_fiber_ring_hom (x : prime_spectrum.Top R) :
    localization_to_stalk R x ≫ stalk_to_fiber_ring_hom R x = 𝟙 _ :=
  (stalk_iso R x).inv_hom_id

/-- The canonical ring homomorphism interpreting `s ∈ R_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def to_basic_open (f : R) : Localization.Away f →+* (structure_sheaf R).1.obj (op $ basic_open f) :=
  IsLocalization.Away.lift f (is_unit_to_basic_open_self R f)

@[simp]
theorem to_basic_open_mk' (s f : R) (g : Submonoid.powers s) :
    to_basic_open R s (IsLocalization.mk' (Localization.Away s) f g) =
      const R f g (basic_open s) fun x hx => Submonoid.powers_subset hx g.2 :=
  (IsLocalization.lift_mk'_spec _ _ _ _).2 $ by
    rw [to_open_eq_const, to_open_eq_const, const_mul_cancel']

@[simp]
theorem localization_to_basic_open (f : R) :
    RingHom.comp (to_basic_open R f) (algebraMap R (Localization.Away f)) = to_open R (basic_open f) :=
  RingHom.ext $ fun g => by
    rw [to_basic_open, IsLocalization.Away.lift, RingHom.comp_apply, IsLocalization.lift_eq]

@[simp]
theorem to_basic_open_to_map (s f : R) :
    to_basic_open R s (algebraMap R (Localization.Away s) f) =
      const R f 1 (basic_open s) fun _ _ => Submonoid.one_mem _ :=
  (IsLocalization.lift_eq _ _).trans $ to_open_eq_const _ _ _

theorem to_basic_open_injective (f : R) : Function.Injective (to_basic_open R f) := by
  intro s t h_eq
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) s
  obtain ⟨c, ⟨d, hd⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
  simp only [to_basic_open_mk'] at h_eq
  rw [IsLocalization.eq]
  let I : Ideal R :=
    { Carrier := { r : R | a * d * r = c * b * r },
      zero_mem' := by
        simp only [Set.mem_set_of_eq, mul_zero],
      add_mem' := fun r₁ r₂ hr₁ hr₂ => by
        dsimp  at hr₁ hr₂⊢
        simp only [mul_addₓ, hr₁, hr₂],
      smul_mem' := fun r₁ r₂ hr₂ => by
        dsimp  at hr₂⊢
        simp only [mul_comm r₁ r₂, ← mul_assoc, hr₂] }
  suffices f ∈ I.radical by
    cases' this with n hn
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩
  rw [← vanishing_ideal_zero_locus_eq_radical, mem_vanishing_ideal]
  intro p hfp
  contrapose hfp
  rw [mem_zero_locus, Set.not_subset]
  have := congr_funₓ (congr_argₓ Subtype.val h_eq) ⟨p, hfp⟩
  rw [const_apply, const_apply, IsLocalization.eq] at this
  cases' this with r hr
  exact ⟨r.1, hr, r.2⟩

theorem locally_const_basic_open (U : opens (prime_spectrum.Top R)) (s : (structure_sheaf R).1.obj (op U)) (x : U) :
    ∃ (f g : R)(i : basic_open g ⟶ U),
      x.1 ∈ basic_open g ∧ (const R f g (basic_open g) fun y hy => hy) = (structure_sheaf R).1.map i.op s :=
  by
  obtain ⟨V, hxV : x.1 ∈ V.1, iVU, f, g, hVDg : V ⊆ basic_open g, s_eq⟩ := exists_const R U s x.1 x.2
  obtain ⟨_, ⟨h, rfl⟩, hxDh, hDhV : basic_open h ⊆ V⟩ :=
    is_topological_basis_basic_opens.exists_subset_of_mem_open hxV V.2
  cases' (basic_open_le_basic_open_iff h g).mp (Set.Subset.trans hDhV hVDg) with n hn
  replace hn := Ideal.mul_mem_left (Ideal.span {g}) h hn
  rw [← pow_succₓ, Ideal.mem_span_singleton'] at hn
  cases' hn with c hc
  have basic_opens_eq :=
    basic_open_pow h (n + 1)
      (by
        linarith)
  have i_basic_open := eq_to_hom basic_opens_eq ≫ hom_of_le hDhV
  use f * c, h ^ (n + 1), i_basic_open ≫ iVU, (basic_opens_eq.symm.le : _) hxDh
  rw [op_comp, functor.map_comp, comp_apply, ← s_eq, res_const]
  swap
  · intro y hy
    rw [basic_opens_eq] at hy
    exact (Set.Subset.trans hDhV hVDg : _) hy
    
  apply const_ext
  rw [mul_assoc f c g, hc]

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (i j «expr ∈ » t)
theorem normalize_finite_fraction_representation (U : opens (prime_spectrum.Top R))
    (s : (structure_sheaf R).1.obj (op U)) {ι : Type _} (t : Finset ι) (a h : ι → R)
    (iDh : ∀ i : ι, basic_open (h i) ⟶ U) (h_cover : U.1 ⊆ ⋃ i ∈ t, (basic_open (h i)).1)
    (hs : ∀ i : ι, (const R (a i) (h i) (basic_open (h i)) fun y hy => hy) = (structure_sheaf R).1.map (iDh i).op s) :
    ∃ (a' h' : ι → R)(iDh' : ∀ i : ι, basic_open (h' i) ⟶ U),
      (U.1 ⊆ ⋃ i ∈ t, (basic_open (h' i)).1) ∧
        (∀ i j _ : i ∈ t _ : j ∈ t, a' i * h' j = h' i * a' j) ∧
          ∀,
            ∀ i ∈ t,
              ∀, (structure_sheaf R).1.map (iDh' i).op s = const R (a' i) (h' i) (basic_open (h' i)) fun y hy => hy :=
  by
  have fractions_eq :
    ∀ i j : ι,
      IsLocalization.mk' (Localization.Away _) (a i * h j) ⟨h i * h j, Submonoid.mem_powers _⟩ =
        IsLocalization.mk' _ (h i * a j) ⟨h i * h j, Submonoid.mem_powers _⟩ :=
    by
    intro i j
    let D := basic_open (h i * h j)
    let iDi : D ⟶ basic_open (h i) := hom_of_le (basic_open_mul_le_left _ _)
    let iDj : D ⟶ basic_open (h j) := hom_of_le (basic_open_mul_le_right _ _)
    apply to_basic_open_injective R (h i * h j)
    rw [to_basic_open_mk', to_basic_open_mk']
    simp only [SetLike.coe_mk]
    trans
    convert congr_argₓ ((structure_sheaf R).1.map iDj.op) (hs j).symm using 1
    convert congr_argₓ ((structure_sheaf R).1.map iDi.op) (hs i) using 1
    swap
    all_goals
      rw [res_const]
      apply const_ext
      ring
    exacts[basic_open_mul_le_right _ _, basic_open_mul_le_left _ _]
  have exists_power : ∀ i j : ι, ∃ n : ℕ, a i * h j * (h i * h j) ^ n = h i * a j * (h i * h j) ^ n := by
    intro i j
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := is_localization.eq.mp (fractions_eq i j)
    use n + 1
    rw [pow_succₓ]
    dsimp  at hc
    convert hc using 1 <;> ring
  let n := fun p : ι × ι => (exists_power p.1 p.2).some
  have n_spec := fun p : ι × ι => (exists_power p.fst p.snd).some_spec
  let N := (t.product t).sup n
  have basic_opens_eq : ∀ i : ι, basic_open (h i ^ (N + 1)) = basic_open (h i) := fun i =>
    basic_open_pow _ _
      (by
        linarith)
  refine' ⟨fun i => a i * h i ^ N, fun i => h i ^ (N + 1), fun i => eq_to_hom (basic_opens_eq i) ≫ iDh i, _, _, _⟩
  · simpa only [basic_opens_eq] using h_cover
    
  · intro i hi j hj
    have n_le_N : n (i, j) ≤ N := Finset.le_sup (finset.mem_product.mpr ⟨hi, hj⟩)
    cases' Nat.Le.dest n_le_N with k hk
    simp only [← hk, pow_addₓ, pow_oneₓ]
    convert congr_argₓ (fun z => z * (h i * h j) ^ k) (n_spec (i, j)) using 1 <;>
      · simp only [n, mul_powₓ]
        ring
        
    
  intro i hi
  rw [op_comp, functor.map_comp, comp_apply, ← hs, res_const]
  swap
  exact (basic_opens_eq i).le
  apply const_ext
  rw [pow_succₓ]
  ring

open_locale Classical

open_locale BigOperators

theorem to_basic_open_surjective (f : R) : Function.Surjective (to_basic_open R f) := by
  intro s
  let ι : Type u := basic_open f
  choose a' h' iDh' hxDh' s_eq' using locally_const_basic_open R (basic_open f) s
  obtain ⟨t, ht_cover'⟩ :=
    (is_compact_basic_open f).elim_finite_subcover (fun i : ι => (basic_open (h' i)).1) (fun i => is_open_basic_open)
      fun x hx => _
  swap
  · rw [Set.mem_Union]
    exact ⟨⟨x, hx⟩, hxDh' ⟨x, hx⟩⟩
    
  obtain ⟨a, h, iDh, ht_cover, ah_ha, s_eq⟩ :=
    normalize_finite_fraction_representation R (basic_open f) s t a' h' iDh' ht_cover' s_eq'
  clear s_eq' iDh' hxDh' ht_cover' a' h'
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (h '' ↑t)).radical := by
    rw [← vanishing_ideal_zero_locus_eq_radical, zero_locus_span]
    simp_rw [Subtype.val_eq_coe, basic_open_eq_zero_locus_compl]  at ht_cover
    rw [Set.compl_subset_comm] at ht_cover
    simp_rw [Set.compl_Union, compl_compl, ← zero_locus_Union, ← Finset.set_bUnion_coe, ← Set.image_eq_Union]  at
      ht_cover
    apply vanishing_ideal_anti_mono ht_cover
    exact subset_vanishing_ideal_zero_locus {f} (Set.mem_singleton f)
  replace hn := Ideal.mul_mem_left _ f hn
  erw [← pow_succₓ, Finsupp.mem_span_image_iff_total] at hn
  rcases hn with ⟨b, b_supp, hb⟩
  rw [Finsupp.total_apply_of_mem_supported R b_supp] at hb
  dsimp  at hb
  use
    IsLocalization.mk' (Localization.Away f) (∑ i : ι in t, b i * a i) (⟨f ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers _)
  rw [to_basic_open_mk']
  let tt := ((t : Set (basic_open f)) : Type u)
  apply (structure_sheaf R).eq_of_locally_eq' (fun i : tt => basic_open (h i)) (basic_open f) fun i : tt => iDh i
  · intro x hx
    erw [TopologicalSpace.Opens.mem_supr]
    have := ht_cover hx
    rw [← Finset.set_bUnion_coe, Set.mem_Union₂] at this
    rcases this with ⟨i, i_mem, x_mem⟩
    use i, i_mem
    
  rintro ⟨i, hi⟩
  dsimp
  change (structure_sheaf R).1.map _ _ = (structure_sheaf R).1.map _ _
  rw [s_eq i hi, res_const]
  swap
  · intro y hy
    change y ∈ basic_open (f ^ (n + 1))
    rw
      [basic_open_pow f (n + 1)
        (by
          linarith)]
    exact (le_of_hom (iDh i) : _) hy
    
  apply const_ext
  rw [← hb, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, ah_ha j hj i hi]
  ring

instance is_iso_to_basic_open (f : R) : is_iso (show CommRingₓₓ.of _ ⟶ _ from to_basic_open R f) :=
  have : is_iso ((forget CommRingₓₓ).map (show CommRingₓₓ.of _ ⟶ _ from to_basic_open R f)) :=
    (is_iso_iff_bijective _).mpr ⟨to_basic_open_injective R f, to_basic_open_surjective R f⟩
  is_iso_of_reflects_iso _ (forget CommRingₓₓ)

/-- The ring isomorphism between the structure sheaf on `basic_open f` and the localization of `R`
at the submonoid of powers of `f`. -/
def basic_open_iso (f : R) : (structure_sheaf R).1.obj (op (basic_open f)) ≅ CommRingₓₓ.of (Localization.Away f) :=
  (as_iso (show CommRingₓₓ.of _ ⟶ _ from to_basic_open R f)).symm

instance stalk_algebra (p : PrimeSpectrum R) : Algebra R ((structure_sheaf R).val.stalk p) :=
  (to_stalk R p).toAlgebra

@[simp]
theorem stalk_algebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structure_sheaf R).val.stalk p) r = to_stalk R p r :=
  rfl

/-- Stalk of the structure sheaf at a prime p as localization of R -/
instance is_localization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structure_sheaf R).val.stalk p) p.as_ideal := by
  convert
    (IsLocalization.is_localization_iff_of_ring_equiv _ (stalk_iso R p).symm.commRingIsoToRingEquiv).mp
      Localization.is_localization
  apply Algebra.algebra_ext
  intro
  rw [stalk_algebra_map]
  congr 1
  erw [iso.eq_comp_inv]
  exact to_stalk_comp_stalk_to_fiber_ring_hom R p

instance open_algebra (U : opens (PrimeSpectrum R)ᵒᵖ) : Algebra R ((structure_sheaf R).val.obj U) :=
  (to_open R (unop U)).toAlgebra

@[simp]
theorem open_algebra_map (U : opens (PrimeSpectrum R)ᵒᵖ) (r : R) :
    algebraMap R ((structure_sheaf R).val.obj U) r = to_open R (unop U) r :=
  rfl

/-- Sections of the structure sheaf of Spec R on a basic open as localization of R -/
instance is_localization.to_basic_open (r : R) :
    IsLocalization.Away r ((structure_sheaf R).val.obj (op $ basic_open r)) := by
  convert
    (IsLocalization.is_localization_iff_of_ring_equiv _ (basic_open_iso R r).symm.commRingIsoToRingEquiv).mp
      Localization.is_localization
  apply Algebra.algebra_ext
  intro x
  congr 1
  exact (localization_to_basic_open R r).symm

instance to_basic_open_epi (r : R) : epi (to_open R (basic_open r)) :=
  ⟨fun S f g h => by
    refine' IsLocalization.ring_hom_ext _ _
    swap 5
    exact is_localization.to_basic_open R r
    exact h⟩

@[elementwise]
theorem to_global_factors :
    to_open R ⊤ =
      CommRingₓₓ.ofHom (algebraMap R (Localization.Away (1 : R))) ≫
        to_basic_open R (1 : R) ≫ (structure_sheaf R).1.map (eq_to_hom basic_open_one.symm).op :=
  by
  change to_open R ⊤ = (to_basic_open R 1).comp _ ≫ _
  unfold CommRingₓₓ.ofHom
  rw [localization_to_basic_open R, to_open_res]

instance is_iso_to_global : is_iso (to_open R ⊤) := by
  let hom := CommRingₓₓ.ofHom (algebraMap R (Localization.Away (1 : R)))
  have : is_iso hom := is_iso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingIso
  rw [to_global_factors R]
  infer_instance

/-- The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`. -/
@[simps]
def global_sections_iso : CommRingₓₓ.of R ≅ (structure_sheaf R).1.obj (op ⊤) :=
  as_iso (to_open R ⊤)

@[simp]
theorem global_sections_iso_hom (R : CommRingₓₓ) : (global_sections_iso R).hom = to_open R ⊤ :=
  rfl

@[simp, reassoc, elementwise]
theorem to_stalk_stalk_specializes {R : Type _} [CommRingₓ R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    to_stalk R y ≫ (structure_sheaf R).val.stalkSpecializes h = to_stalk R x := by
  dsimp [to_stalk]
  simpa

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:57:31: expecting tactic arg
@[simp, reassoc, elementwise]
theorem localization_to_stalk_stalk_specializes {R : Type _} [CommRingₓ R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    structure_sheaf.localization_to_stalk R y ≫ (structure_sheaf R).val.stalkSpecializes h =
      CommRingₓₓ.ofHom (PrimeSpectrum.localizationMapOfSpecializes h) ≫ structure_sheaf.localization_to_stalk R x :=
  by
  apply IsLocalization.ring_hom_ext y.as_ideal.prime_compl
  any_goals {
  }
  erw [RingHom.comp_assoc]
  conv_rhs => erw [RingHom.comp_assoc]
  dsimp [CommRingₓₓ.ofHom, localization_to_stalk, PrimeSpectrum.localizationMapOfSpecializes]
  rw [IsLocalization.lift_comp, IsLocalization.lift_comp, IsLocalization.lift_comp]
  exact to_stalk_stalk_specializes h

@[simp, reassoc, elementwise]
theorem stalk_specializes_stalk_to_fiber {R : Type _} [CommRingₓ R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    (structure_sheaf R).val.stalkSpecializes h ≫ structure_sheaf.stalk_to_fiber_ring_hom R x =
      structure_sheaf.stalk_to_fiber_ring_hom R y ≫ PrimeSpectrum.localizationMapOfSpecializes h :=
  by
  change _ ≫ (structure_sheaf.stalk_iso R x).hom = (structure_sheaf.stalk_iso R y).hom ≫ _
  rw [← iso.eq_comp_inv, category.assoc, ← iso.inv_comp_eq]
  exact localization_to_stalk_stalk_specializes h

section Comap

variable {R} {S : Type u} [CommRingₓ S] {P : Type u} [CommRingₓ P]

/-- Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum of `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can push a section `s`
on `U` to a section on `V`, by composing with `localization.local_ring_hom _ _ f` from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, localizations R x`. Below,
we prove the predicate `is_locally_fraction` is preserved by this map, hence it can be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
def comap_fun (f : R →+* S) (U : opens (prime_spectrum.Top R)) (V : opens (prime_spectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : ∀ x : U, localizations R x) (y : V) : localizations S y :=
  Localization.localRingHom (PrimeSpectrum.comap f y.1).asIdeal _ f rfl (s ⟨PrimeSpectrum.comap f y.1, hUV y.2⟩ : _)

theorem comap_fun_is_locally_fraction (f : R →+* S) (U : opens (prime_spectrum.Top R))
    (V : opens (prime_spectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : ∀ x : U, localizations R x)
    (hs : (is_locally_fraction R).toPrelocalPredicate.pred s) :
    (is_locally_fraction S).toPrelocalPredicate.pred (comap_fun f U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨PrimeSpectrum.comap f p, hUV hpV⟩ with ⟨W, m, iWU, a, b, h_frac⟩
  refine' ⟨opens.comap (comap f) W⊓V, ⟨m, hpV⟩, opens.inf_le_right _ _, f a, f b, _⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  specialize h_frac ⟨PrimeSpectrum.comap f q, hqW⟩
  refine' ⟨h_frac.1, _⟩
  dsimp only [comap_fun]
  erw [← Localization.local_ring_hom_to_map (PrimeSpectrum.comap f q).asIdeal, ← RingHom.map_mul, h_frac.2,
    Localization.local_ring_hom_to_map]
  rfl

/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
def comap (f : R →+* S) (U : opens (prime_spectrum.Top R)) (V : opens (prime_spectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (structure_sheaf R).1.obj (op U) →+* (structure_sheaf S).1.obj (op V) where
  toFun := fun s => ⟨comap_fun f U V hUV s.1, comap_fun_is_locally_fraction f U V hUV s.1 s.2⟩
  map_one' :=
    Subtype.ext $
      funext $ fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_one, Pi.one_apply,
          RingHom.map_one]
        rfl
  map_zero' :=
    Subtype.ext $
      funext $ fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_zero, Pi.zero_apply,
          RingHom.map_zero]
        rfl
  map_add' := fun s t =>
    Subtype.ext $
      funext $ fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_add, Pi.add_apply,
          RingHom.map_add]
        rfl
  map_mul' := fun s t =>
    Subtype.ext $
      funext $ fun p => by
        rw [Subtype.coe_mk, Subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_mul, Pi.mul_apply,
          RingHom.map_mul]
        rfl

@[simp]
theorem comap_apply (f : R →+* S) (U : opens (prime_spectrum.Top R)) (V : opens (prime_spectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : (structure_sheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩ : _) :=
  rfl

theorem comap_const (f : R →+* S) (U : opens (prime_spectrum.Top R)) (V : opens (prime_spectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : ∀ x : PrimeSpectrum R, x ∈ U → b ∈ x.as_ideal.prime_compl) :
    comap f U V hUV (const R a b U hb) = const S (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
  Subtype.eq $
    funext $ fun p => by
      rw [comap_apply, const_apply, const_apply]
      erw [Localization.local_ring_hom_mk']
      rfl

/-- For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the identity from OO_X(U)
to OO_X(U) is the identity.
-/
theorem comap_id_eq_map (U V : opens (prime_spectrum.Top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun p hpV =>
        le_of_hom iVU $ by
          rwa [PrimeSpectrum.comap_id]) =
      (structure_sheaf R).1.map iVU.op :=
  RingHom.ext $ fun s =>
    Subtype.eq $
      funext $ fun p => by
        rw [comap_apply]
        obtain ⟨W, hpW, iWU, h⟩ := s.2 (iVU p)
        obtain ⟨a, b, h'⟩ := h.eq_mk'
        obtain ⟨hb₁, s_eq₁⟩ := h' ⟨p, hpW⟩
        obtain ⟨hb₂, s_eq₂⟩ :=
          h'
            ⟨PrimeSpectrum.comap (RingHom.id _) p.1, by
              rwa [PrimeSpectrum.comap_id]⟩
        dsimp only  at s_eq₁ s_eq₂
        erw [s_eq₂, Localization.local_ring_hom_mk', ← s_eq₁, ← res_apply]

/-- The comap of the identity is the identity. In this variant of the lemma, two open subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is be useful when `U` and `V`
are not definitionally equal.
-/
theorem comap_id (U V : opens (prime_spectrum.Top R)) (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by
        rwa [hUV, PrimeSpectrum.comap_id]) =
      eq_to_hom
        (show (structure_sheaf R).1.obj (op U) = _ by
          rw [hUV]) :=
  by
  erw [comap_id_eq_map U V (eq_to_hom hUV.symm), eq_to_hom_op, eq_to_hom_map]

@[simp]
theorem comap_id' (U : opens (prime_spectrum.Top R)) :
    (comap (RingHom.id R) U U fun p hpU => by
        rwa [PrimeSpectrum.comap_id]) =
      RingHom.id _ :=
  by
  rw [comap_id U U rfl]
  rfl

theorem comap_comp (f : R →+* S) (g : S →+* P) (U : opens (prime_spectrum.Top R)) (V : opens (prime_spectrum.Top S))
    (W : opens (prime_spectrum.Top P)) (hUV : ∀, ∀ p ∈ V, ∀, PrimeSpectrum.comap f p ∈ U)
    (hVW : ∀, ∀ p ∈ W, ∀, PrimeSpectrum.comap g p ∈ V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext $ fun s =>
    Subtype.eq $
      funext $ fun p => by
        rw [comap_apply]
        erw [Localization.local_ring_hom_comp _ (PrimeSpectrum.comap g p.1).asIdeal]
        rfl

@[elementwise, reassoc]
theorem to_open_comp_comap (f : R →+* S) (U : opens (prime_spectrum.Top R)) :
    (to_open R U ≫ comap f U (opens.comap (PrimeSpectrum.comap f) U) fun _ => id) = CommRingₓₓ.ofHom f ≫ to_open S _ :=
  RingHom.ext $ fun s =>
    Subtype.eq $
      funext $ fun p => by
        simp_rw [comp_apply, comap_apply, Subtype.val_eq_coe]
        erw [Localization.local_ring_hom_to_map]
        rfl

end Comap

end StructureSheaf

end AlgebraicGeometry

