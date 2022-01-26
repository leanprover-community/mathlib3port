import Mathbin.Analysis.Normed.Group.SemiNormedGroup
import Mathbin.Analysis.Normed.Group.Quotient
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in SemiNormedGroup₁ and SemiNormedGroup

We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels. We also show that
`SemiNormedGroup` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/


open CategoryTheory CategoryTheory.Limits

universe u

namespace SemiNormedGroup₁

noncomputable section

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_cocone {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) : cofork f 0 :=
  cofork.of_π
    (@SemiNormedGroup₁.mkHom _ (SemiNormedGroupₓ.of (Y ⧸ NormedGroupHom.range f.1)) f.1.range.normedMk
      (NormedGroupHom.is_quotient_quotient _).norm_le)
    (by
      ext
      simp only [comp_apply, limits.zero_comp, NormedGroupHom.zero_apply, SemiNormedGroup₁.mk_hom_apply,
        SemiNormedGroup₁.zero_apply, ← NormedGroupHom.mem_ker, f.1.range.ker_normed_mk, f.1.mem_range]
      use x
      rfl)

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_lift {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) (s : cokernel_cofork f) : (cokernel_cocone f).x ⟶ s.X := by
  fconstructor
  · apply NormedGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
    
  exact NormedGroupHom.lift_norm_noninc _ _ _ s.π.2

instance : has_cokernels SemiNormedGroup₁.{u} where
  HasColimit := fun X Y f =>
    has_colimit.mk
      { Cocone := cokernel_cocone f,
        IsColimit :=
          is_colimit_aux _ (cokernel_lift f)
            (fun s => by
              ext
              apply NormedGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp )
            fun s m w => Subtype.eq (NormedGroupHom.lift_unique f.1.range _ _ _ (congr_argₓ Subtype.val w : _)) }

example : has_cokernels SemiNormedGroup₁ := by
  infer_instance

end SemiNormedGroup₁

namespace SemiNormedGroupₓ

section EqualizersAndKernels

/-- The equalizer cone for a parallel pair of morphisms of seminormed groups. -/
def parallel_pair_cone {V W : SemiNormedGroupₓ.{u}} (f g : V ⟶ W) : cone (parallel_pair f g) :=
  @fork.of_ι _ _ _ _ _ _ (of (f - g).ker) (NormedGroupHom.incl (f - g).ker) <| by
    ext v
    have : v.1 ∈ (f - g).ker := v.2
    simpa only [NormedGroupHom.incl_apply, Pi.zero_apply, coe_comp, NormedGroupHom.coe_zero, Subtype.val_eq_coe,
      NormedGroupHom.mem_ker, NormedGroupHom.coe_sub, Pi.sub_apply, sub_eq_zero] using this

instance has_limit_parallel_pair {V W : SemiNormedGroupₓ.{u}} (f g : V ⟶ W) : has_limit (parallel_pair f g) where
  exists_limit :=
    Nonempty.intro
      { Cone := parallel_pair_cone f g,
        IsLimit :=
          fork.is_limit.mk _
            (fun c =>
              NormedGroupHom.ker.lift (fork.ι c) _ <|
                show NormedGroupHom.compHom (f - g) c.ι = 0 by
                  rw [AddMonoidHom.map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
                  exact c.condition)
            (fun c => NormedGroupHom.ker.incl_comp_lift _ _ _) fun c g h => by
            ext x
            dsimp
            rw [← h]
            rfl }

instance : limits.has_equalizers.{u, u + 1} SemiNormedGroupₓ :=
  (@has_equalizers_of_has_limit_parallel_pair SemiNormedGroupₓ _) fun V W f g =>
    SemiNormedGroupₓ.has_limit_parallel_pair f g

end EqualizersAndKernels

section Cokernel

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernel_cocone {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : cofork f 0 :=
  @cofork.of_π _ _ _ _ _ _ (SemiNormedGroupₓ.of (Y ⧸ NormedGroupHom.range f)) f.range.normed_mk
    (by
      ext
      simp only [comp_apply, limits.zero_comp, NormedGroupHom.zero_apply, ← NormedGroupHom.mem_ker,
        f.range.ker_normed_mk, f.mem_range, exists_apply_eq_applyₓ])

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernel_lift {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) (s : cokernel_cofork f) : (cokernel_cocone f).x ⟶ s.X :=
  NormedGroupHom.lift _ s.π
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp )

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def is_colimit_cokernel_cocone {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : is_colimit (cokernel_cocone f) :=
  is_colimit_aux _ (cokernel_lift f)
    (fun s => by
      ext
      apply NormedGroupHom.lift_mk f.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp )
    fun s m w => NormedGroupHom.lift_unique f.range _ _ _ w

instance : has_cokernels SemiNormedGroupₓ.{u} where
  HasColimit := fun X Y f => has_colimit.mk { Cocone := cokernel_cocone f, IsColimit := is_colimit_cokernel_cocone f }

example : has_cokernels SemiNormedGroupₓ := by
  infer_instance

section ExplicitCokernel

/-- An explicit choice of cokernel, which has good properties with respect to the norm. -/
def explicit_cokernel {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : SemiNormedGroupₓ.{u} :=
  (cokernel_cocone f).x

/-- Descend to the explicit cokernel. -/
def explicit_cokernel_desc {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicit_cokernel f ⟶ Z :=
  (is_colimit_cokernel_cocone f).desc
    (cofork.of_π g
      (by
        simp [w]))

/-- The projection from `Y` to the explicit cokernel of `X ⟶ Y`. -/
def explicit_cokernel_π {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : Y ⟶ explicit_cokernel f :=
  (cokernel_cocone f).ι.app walking_parallel_pair.one

theorem explicit_cokernel_π_surjective {X Y : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} :
    Function.Surjective (explicit_cokernel_π f) :=
  surjective_quot_mk _

@[simp, reassoc]
theorem comp_explicit_cokernel_π {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : f ≫ explicit_cokernel_π f = 0 := by
  convert (cokernel_cocone f).w walking_parallel_pair_hom.left
  simp

@[simp]
theorem explicit_cokernel_π_apply_dom_eq_zero {X Y : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} (x : X) :
    (explicit_cokernel_π f) (f x) = 0 :=
  show (f ≫ explicit_cokernel_π f) x = 0 by
    rw [comp_explicit_cokernel_π]
    rfl

@[simp, reassoc]
theorem explicit_cokernel_π_desc {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicit_cokernel_π f ≫ explicit_cokernel_desc w = g :=
  (is_colimit_cokernel_cocone f).fac _ _

@[simp]
theorem explicit_cokernel_π_desc_apply {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {cond : f ≫ g = 0}
    (x : Y) : explicit_cokernel_desc cond (explicit_cokernel_π f x) = g x :=
  show (explicit_cokernel_π f ≫ explicit_cokernel_desc cond) x = g x by
    rw [explicit_cokernel_π_desc]

theorem explicit_cokernel_desc_unique {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0)
    (e : explicit_cokernel f ⟶ Z) (he : explicit_cokernel_π f ≫ e = g) : e = explicit_cokernel_desc w := by
  apply
    (is_colimit_cokernel_cocone f).uniq
      (cofork.of_π g
        (by
          simp [w]))
  rintro (_ | _)
  · convert w.symm
    simp
    
  · exact he
    

theorem explicit_cokernel_desc_comp_eq_desc {X Y Z W : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    {cond : f ≫ g = 0} :
    explicit_cokernel_desc cond ≫ h =
      explicit_cokernel_desc
        (show f ≫ g ≫ h = 0 by
          rw [← CategoryTheory.Category.assoc, cond, limits.zero_comp]) :=
  by
  refine' explicit_cokernel_desc_unique _ _ _
  rw [← CategoryTheory.Category.assoc, explicit_cokernel_π_desc]

@[simp]
theorem explicit_cokernel_desc_zero {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} :
    explicit_cokernel_desc (show f ≫ (0 : Y ⟶ Z) = 0 from CategoryTheory.Limits.comp_zero) = 0 :=
  Eq.symm <| explicit_cokernel_desc_unique _ _ CategoryTheory.Limits.comp_zero

@[ext]
theorem explicit_cokernel_hom_ext {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} (e₁ e₂ : explicit_cokernel f ⟶ Z)
    (h : explicit_cokernel_π f ≫ e₁ = explicit_cokernel_π f ≫ e₂) : e₁ = e₂ := by
  let g : Y ⟶ Z := explicit_cokernel_π f ≫ e₂
  have w : f ≫ g = 0 := by
    simp
  have : e₂ = explicit_cokernel_desc w := by
    apply explicit_cokernel_desc_unique
    rfl
  rw [this]
  apply explicit_cokernel_desc_unique
  exact h

instance explicit_cokernel_π.epi {X Y : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} : epi (explicit_cokernel_π f) := by
  constructor
  intro Z g h H
  ext x
  obtain ⟨x, hx⟩ := explicit_cokernel_π_surjective (explicit_cokernel_π f x)
  change (explicit_cokernel_π f ≫ g) _ = _
  rw [H]

theorem is_quotient_explicit_cokernel_π {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) :
    NormedGroupHom.IsQuotient (explicit_cokernel_π f) :=
  NormedGroupHom.is_quotient_quotient _

theorem norm_noninc_explicit_cokernel_π {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : (explicit_cokernel_π f).NormNoninc :=
  (is_quotient_explicit_cokernel_π f).norm_le

open_locale Nnreal

theorem explicit_cokernel_desc_norm_le_of_norm_le {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0)
    (c : ℝ≥0 ) (h : ∥g∥ ≤ c) : ∥explicit_cokernel_desc w∥ ≤ c :=
  NormedGroupHom.lift_norm_le _ _ _ h

theorem explicit_cokernel_desc_norm_noninc {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {cond : f ≫ g = 0}
    (hg : g.norm_noninc) : (explicit_cokernel_desc cond).NormNoninc := by
  refine' NormedGroupHom.NormNoninc.norm_noninc_iff_norm_le_one.2 _
  rw [← Nnreal.coe_one]
  exact explicit_cokernel_desc_norm_le_of_norm_le cond 1 (NormedGroupHom.NormNoninc.norm_noninc_iff_norm_le_one.1 hg)

theorem explicit_cokernel_desc_comp_eq_zero {X Y Z W : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    (cond : f ≫ g = 0) (cond2 : g ≫ h = 0) : explicit_cokernel_desc cond ≫ h = 0 := by
  rw [← cancel_epi (explicit_cokernel_π f), ← category.assoc, explicit_cokernel_π_desc]
  simp [cond2]

theorem explicit_cokernel_desc_norm_le {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    ∥explicit_cokernel_desc w∥ ≤ ∥g∥ :=
  explicit_cokernel_desc_norm_le_of_norm_le w ∥g∥₊ (le_reflₓ _)

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
def explicit_cokernel_iso {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) : explicit_cokernel f ≅ cokernel f :=
  (is_colimit_cokernel_cocone f).coconePointUniqueUpToIso (colimit.is_colimit _)

@[simp]
theorem explicit_cokernel_iso_hom_π {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) :
    explicit_cokernel_π f ≫ (explicit_cokernel_iso f).hom = cokernel.π _ := by
  simp [explicit_cokernel_π, explicit_cokernel_iso]

@[simp]
theorem explicit_cokernel_iso_inv_π {X Y : SemiNormedGroupₓ.{u}} (f : X ⟶ Y) :
    cokernel.π f ≫ (explicit_cokernel_iso f).inv = explicit_cokernel_π f := by
  simp [explicit_cokernel_π, explicit_cokernel_iso]

@[simp]
theorem explicit_cokernel_iso_hom_desc {X Y Z : SemiNormedGroupₓ.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    (explicit_cokernel_iso f).hom ≫ cokernel.desc f g w = explicit_cokernel_desc w := by
  ext1
  simp [explicit_cokernel_desc, explicit_cokernel_π, explicit_cokernel_iso]

/-- A special case of `category_theory.limits.cokernel.map` adapted to `explicit_cokernel`. -/
noncomputable def explicit_cokernel.map {A B C D : SemiNormedGroupₓ.{u}} {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C}
    {fcd : C ⟶ D} (h : fab ≫ fbd = fac ≫ fcd) : explicit_cokernel fab ⟶ explicit_cokernel fcd :=
  @explicit_cokernel_desc _ _ _ fab (fbd ≫ explicit_cokernel_π _) <| by
    simp [reassoc_of h]

/-- A special case of `category_theory.limits.cokernel.map_desc` adapted to `explicit_cokernel`. -/
theorem explicit_coker.map_desc {A B C D B' D' : SemiNormedGroupₓ.{u}} {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C}
    {fcd : C ⟶ D} {h : fab ≫ fbd = fac ≫ fcd} {fbb' : B ⟶ B'} {fdd' : D ⟶ D'} {condb : fab ≫ fbb' = 0}
    {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'} (h' : fbb' ≫ g = fbd ≫ fdd') :
    explicit_cokernel_desc condb ≫ g = explicit_cokernel.map h ≫ explicit_cokernel_desc condd := by
  delta' explicit_cokernel.map
  simp [← cancel_epi (explicit_cokernel_π fab), category.assoc, explicit_cokernel_π_desc, h']

end ExplicitCokernel

end Cokernel

end SemiNormedGroupₓ

