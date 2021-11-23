import Mathbin.Order.WellFoundedSet 
import Mathbin.Algebra.BigOperators.Finprod 
import Mathbin.RingTheory.Valuation.Basic 
import Mathbin.Algebra.Module.Pi 
import Mathbin.RingTheory.PowerSeries.Basic

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `hahn_series Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `hahn_series Γ R` is a
valued field, with value group `Γ`.

These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `ring_theory/laurent_series`.

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.
  * `hahn_series.add_val Γ R` defines an `add_valuation` on `hahn_series Γ R` when `Γ` is linearly
    ordered.
  * A `hahn_series.summable_family` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `hahn_series.summable_family.hsum`, which can be bundled as a `linear_map` as
  `hahn_series.summable_family.lsum`. Note that this is different from `summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `hahn_series.summable_family`, and formally summable families whose sums do not converge
  topologically.
  * Laurent series over `R` are implemented as `hahn_series ℤ R` in the file
    `ring_theory/laurent_series`.

## TODO
  * Build an API for the variable `X` (defined to be `single 1 1 : hahn_series Γ R`) in analogy to
    `X : polynomial R` and `X : power_series R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]

-/


open Finset

open_locale BigOperators Classical Pointwise

noncomputable theory

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries(Γ : Type _)(R : Type _)[PartialOrderₓ Γ][HasZero R] where 
  coeff : Γ → R 
  is_pwo_support' : (Function.Support coeff).IsPwo

variable{Γ : Type _}{R : Type _}

namespace HahnSeries

section Zero

variable[PartialOrderₓ Γ][HasZero R]

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
def support (x : HahnSeries Γ R) : Set Γ :=
  Function.Support x.coeff

@[simp]
theorem is_pwo_support (x : HahnSeries Γ R) : x.support.is_pwo :=
  x.is_pwo_support'

@[simp]
theorem is_wf_support (x : HahnSeries Γ R) : x.support.is_wf :=
  x.is_pwo_support.is_wf

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _

instance  : HasZero (HahnSeries Γ R) :=
  ⟨{ coeff := 0,
      is_pwo_support' :=
        by 
          simp  }⟩

instance  : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance  [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun a b => a.ext b (Subsingleton.elimₓ _ _)⟩

@[simp]
theorem zero_coeff {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl

theorem ne_zero_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ zero_coeff : x.coeff g = 0)) h

@[simp]
theorem support_zero : support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem support_nonempty_iff {x : hahn_series Γ R} : «expr ↔ »(x.support.nonempty, «expr ≠ »(x, 0)) :=
begin
  split,
  { rintro ["⟨", ident a, ",", ident ha, "⟩", ident rfl],
    apply [expr ha zero_coeff] },
  { contrapose ["!"] [],
    rw [expr set.not_nonempty_iff_eq_empty] [],
    intro [ident h],
    ext [] [ident a] [],
    have [ident ha] [] [":=", expr set.not_mem_empty a],
    rw ["[", "<-", expr h, ",", expr mem_support, ",", expr not_not, "]"] ["at", ident ha],
    rw ["[", expr ha, ",", expr zero_coeff, "]"] [] }
end

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) :=
  { toFun :=
      fun r => { coeff := Pi.single a r, is_pwo_support' := (Set.is_pwo_singleton a).mono Pi.support_single_subset },
    map_zero' := ext _ _ (Pi.single_zero _) }

variable{a b : Γ}{r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r :=
  Pi.single_eq_same a r

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 :=
  Pi.single_eq_of_ne h r

theorem single_coeff : (single a r).coeff b = if b = a then r else 0 :=
  by 
    splitIfs with h <;> simp [h]

@[simp]
theorem support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
  Pi.support_single_of_ne h

theorem support_single_subset : support (single a r) ⊆ {a} :=
  Pi.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h

@[simp]
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs =>
    by 
      rw [←single_coeff_same a r, ←single_coeff_same a s, rs]

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 :=
  fun con => h (single_injective a (Con.trans single_eq_zero.symm))

instance  [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by 
      obtain ⟨r, s, rs⟩ := exists_pair_ne R 
      inhabit Γ 
      refine' ⟨single (arbitraryₓ Γ) r, single (arbitraryₓ Γ) s, fun con => rs _⟩
      rw [←single_coeff_same (arbitraryₓ Γ) r, Con, single_coeff_same]⟩

section Order

variable[HasZero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.is_wf_support.min (support_nonempty_iff.2 h)

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : order x = x.is_wf_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  by 
    rw [order_of_ne hx]
    exact x.is_wf_support.min_mem (support_nonempty_iff.2 hx)

theorem order_le_of_coeff_ne_zero {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x : HahnSeries Γ R} {g : Γ}
  (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_transₓ (le_of_eqₓ (order_of_ne (ne_zero_of_coeff_ne_zero h))) (Set.IsWf.min_le _ _ ((mem_support _ _).2 h))

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset ((single a r).is_wf_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))

end Order

section Domain

variable{Γ' : Type _}[PartialOrderₓ Γ']

/-- Extends the domain of a `hahn_series` by an `order_embedding`. -/
def emb_domain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R :=
  fun x =>
    { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.some h) else 0,
      is_pwo_support' :=
        (x.is_pwo_support.image_of_monotone f.monotone).mono
          fun b hb =>
            by 
              contrapose! hb 
              rw [Function.mem_support, dif_neg hb, not_not] }

@[simp]
theorem emb_domain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} : (emb_domain f x).coeff (f a) = x.coeff a :=
  by 
    rw [emb_domain]
    dsimp only 
    byCases' ha : a ∈ x.support
    ·
      rw [dif_pos (Set.mem_image_of_mem f ha)]
      exact congr rfl (f.injective (Classical.some_spec (Set.mem_image_of_mem f ha)).2)
    ·
      rw [dif_neg, not_not.1 fun c => ha ((mem_support _ _).2 c)]
      contrapose! ha 
      obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha 
      rwa [f.injective hb2] at hb1

@[simp]
theorem emb_domain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f) (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g')
  {x : HahnSeries Γ R} {a : Γ} : (emb_domain ⟨⟨f, hfi⟩, hf⟩ x).coeff (f a) = x.coeff a :=
  emb_domain_coeff

theorem emb_domain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ f '' x.support) :
  (emb_domain f x).coeff b = 0 :=
  dif_neg hb

theorem support_emb_domain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} : support (emb_domain f x) ⊆ f '' x.support :=
  by 
    intro g hg 
    contrapose! hg 
    rw [mem_support, emb_domain_notin_image_support hg, not_not]

theorem emb_domain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.Range f) :
  (emb_domain f x).coeff b = 0 :=
  emb_domain_notin_image_support fun con => hb (Set.image_subset_range _ _ Con)

@[simp]
theorem emb_domain_zero {f : Γ ↪o Γ'} : emb_domain f (0 : HahnSeries Γ R) = 0 :=
  by 
    ext 
    simp [emb_domain_notin_image_support]

@[simp]
theorem emb_domain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} : emb_domain f (single g r) = single (f g) r :=
  by 
    ext g' 
    byCases' h : g' = f g
    ·
      simp [h]
    rw [emb_domain_notin_image_support, single_coeff_of_ne h]
    byCases' hr : r = 0
    ·
      simp [hr]
    rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem emb_domain_injective
{f : «expr ↪o »(Γ, Γ')} : function.injective (emb_domain f : hahn_series Γ R → hahn_series Γ' R) :=
λ x y xy, begin
  ext [] [ident g] [],
  rw ["[", expr ext_iff, ",", expr function.funext_iff, "]"] ["at", ident xy],
  have [ident xyg] [] [":=", expr xy (f g)],
  rwa ["[", expr emb_domain_coeff, ",", expr emb_domain_coeff, "]"] ["at", ident xyg]
end

end Domain

end Zero

section Addition

variable[PartialOrderₓ Γ]

section AddMonoidₓ

variable[AddMonoidₓ R]

instance  : Add (HahnSeries Γ R) :=
  { add :=
      fun x y =>
        { coeff := x.coeff+y.coeff,
          is_pwo_support' := (x.is_pwo_support.union y.is_pwo_support).mono (Function.support_add _ _) } }

instance  : AddMonoidₓ (HahnSeries Γ R) :=
  { zero := 0, add := ·+·,
    add_assoc :=
      fun x y z =>
        by 
          ext 
          apply add_assocₓ,
    zero_add :=
      fun x =>
        by 
          ext 
          apply zero_addₓ,
    add_zero :=
      fun x =>
        by 
          ext 
          apply add_zeroₓ }

@[simp]
theorem add_coeff' {x y : HahnSeries Γ R} : (x+y).coeff = x.coeff+y.coeff :=
  rfl

theorem add_coeff {x y : HahnSeries Γ R} {a : Γ} : (x+y).coeff a = x.coeff a+y.coeff a :=
  rfl

theorem support_add_subset {x y : HahnSeries Γ R} : support (x+y) ⊆ support x ∪ support y :=
  fun a ha =>
    by 
      rw [mem_support, add_coeff] at ha 
      rw [Set.mem_union, mem_support, mem_support]
      contrapose! ha 
      rw [ha.1, ha.2, add_zeroₓ]

theorem min_order_le_order_add {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0)
  (hxy : (x+y) ≠ 0) : min x.order y.order ≤ (x+y).order :=
  by 
    rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
    refine' le_transₓ _ (Set.IsWf.min_le_min_of_subset support_add_subset)
    ·
      exact x.is_wf_support.union y.is_wf_support
    ·
      exact Set.Nonempty.mono (Set.subset_union_left _ _) (support_nonempty_iff.2 hx)
    rw [Set.IsWf.min_union]

/-- `single` as an additive monoid/group homomorphism -/
@[simps]
def single.add_monoid_hom (a : Γ) : R →+ HahnSeries Γ R :=
  { single a with
    map_add' :=
      fun x y =>
        by 
          ext b 
          byCases' h : b = a <;> simp [h] }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
def coeff.add_monoid_hom (g : Γ) : HahnSeries Γ R →+ R :=
  { toFun := fun f => f.coeff g, map_zero' := zero_coeff, map_add' := fun x y => add_coeff }

section Domain

variable{Γ' : Type _}[PartialOrderₓ Γ']

theorem emb_domain_add (f : Γ ↪o Γ') (x y : HahnSeries Γ R) : emb_domain f (x+y) = emb_domain f x+emb_domain f y :=
  by 
    ext g 
    byCases' hg : g ∈ Set.Range f
    ·
      obtain ⟨a, rfl⟩ := hg 
      simp 
    ·
      simp [emb_domain_notin_range, hg]

end Domain

end AddMonoidₓ

instance  [AddCommMonoidₓ R] : AddCommMonoidₓ (HahnSeries Γ R) :=
  { HahnSeries.addMonoid with
    add_comm :=
      fun x y =>
        by 
          ext 
          apply add_commₓ }

section AddGroupₓ

variable[AddGroupₓ R]

instance  : AddGroupₓ (HahnSeries Γ R) :=
  { HahnSeries.addMonoid with
    neg :=
      fun x =>
        { coeff := fun a => -x.coeff a,
          is_pwo_support' :=
            by 
              rw [Function.support_neg]
              exact x.is_pwo_support },
    add_left_neg :=
      fun x =>
        by 
          ext 
          apply add_left_negₓ }

@[simp]
theorem neg_coeff' {x : HahnSeries Γ R} : (-x).coeff = -x.coeff :=
  rfl

theorem neg_coeff {x : HahnSeries Γ R} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl

@[simp]
theorem support_neg {x : HahnSeries Γ R} : (-x).Support = x.support :=
  by 
    ext 
    simp 

@[simp]
theorem sub_coeff' {x y : HahnSeries Γ R} : (x - y).coeff = x.coeff - y.coeff :=
  by 
    ext 
    simp [sub_eq_add_neg]

theorem sub_coeff {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a :=
  by 
    simp 

end AddGroupₓ

instance  [AddCommGroupₓ R] : AddCommGroupₓ (HahnSeries Γ R) :=
  { HahnSeries.addCommMonoid, HahnSeries.addGroup with  }

end Addition

section DistribMulAction

variable[PartialOrderₓ Γ]{V : Type _}[Monoidₓ R][AddMonoidₓ V][DistribMulAction R V]

instance  : HasScalar R (HahnSeries Γ V) :=
  ⟨fun r x =>
      { coeff := r • x.coeff, is_pwo_support' := x.is_pwo_support.mono (Function.support_smul_subset_right r x.coeff) }⟩

@[simp]
theorem smul_coeff {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl

instance  : DistribMulAction R (HahnSeries Γ V) :=
  { smul := · • ·,
    one_smul :=
      fun _ =>
        by 
          ext 
          simp ,
    smul_zero :=
      fun _ =>
        by 
          ext 
          simp ,
    smul_add :=
      fun _ _ _ =>
        by 
          ext 
          simp [smul_add],
    mul_smul :=
      fun _ _ _ =>
        by 
          ext 
          simp [mul_smul] }

variable{S : Type _}[Monoidₓ S][DistribMulAction S V]

instance  [HasScalar R S] [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) :=
  ⟨fun r s a =>
      by 
        ext 
        simp ⟩

instance  [SmulCommClass R S V] : SmulCommClass R S (HahnSeries Γ V) :=
  ⟨fun r s a =>
      by 
        ext 
        simp [smul_comm]⟩

end DistribMulAction

section Module

variable[PartialOrderₓ Γ][Semiringₓ R]{V : Type _}[AddCommMonoidₓ V][Module R V]

instance  : Module R (HahnSeries Γ V) :=
  { HahnSeries.distribMulAction with
    zero_smul :=
      fun _ =>
        by 
          ext 
          simp ,
    add_smul :=
      fun _ _ _ =>
        by 
          ext 
          simp [add_smul] }

/-- `single` as a linear map -/
@[simps]
def single.linear_map (a : Γ) : R →ₗ[R] HahnSeries Γ R :=
  { single.add_monoid_hom a with
    map_smul' :=
      fun r s =>
        by 
          ext b 
          byCases' h : b = a <;> simp [h] }

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linear_map (g : Γ) : HahnSeries Γ R →ₗ[R] R :=
  { coeff.add_monoid_hom g with map_smul' := fun r s => rfl }

section Domain

variable{Γ' : Type _}[PartialOrderₓ Γ']

theorem emb_domain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) : emb_domain f (r • x) = r • emb_domain f x :=
  by 
    ext g 
    byCases' hg : g ∈ Set.Range f
    ·
      obtain ⟨a, rfl⟩ := hg 
      simp 
    ·
      simp [emb_domain_notin_range, hg]

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def emb_domain_linear_map (f : Γ ↪o Γ') : HahnSeries Γ R →ₗ[R] HahnSeries Γ' R :=
  { toFun := emb_domain f, map_add' := emb_domain_add f, map_smul' := emb_domain_smul f }

end Domain

end Module

section Multiplication

variable[OrderedCancelAddCommMonoid Γ]

instance  [HasZero R] [HasOne R] : HasOne (HahnSeries Γ R) :=
  ⟨single 0 1⟩

@[simp]
theorem one_coeff [HasZero R] [HasOne R] {a : Γ} : (1 : HahnSeries Γ R).coeff a = if a = 0 then 1 else 0 :=
  single_coeff

@[simp]
theorem single_zero_one [HasZero R] [HasOne R] : single 0 (1 : R) = 1 :=
  rfl

@[simp]
theorem support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : HahnSeries Γ R) = {0} :=
  support_single_of_ne one_ne_zero

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem order_one [mul_zero_one_class R] : «expr = »(order (1 : hahn_series Γ R), 0) :=
begin
  cases [expr subsingleton_or_nontrivial R] ["with", ident h, ident h]; haveI [] [] [":=", expr h],
  { rw ["[", expr subsingleton.elim (1 : hahn_series Γ R) 0, ",", expr order_zero, "]"] [] },
  { exact [expr order_single one_ne_zero] }
end

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance [non_unital_non_assoc_semiring R] : has_mul (hahn_series Γ R) :=
{ mul := λ
  x
  y, { coeff := λ
    a, «expr∑ in , »((ij), add_antidiagonal x.is_pwo_support y.is_pwo_support a, «expr * »(x.coeff ij.fst, y.coeff ij.snd)),
    is_pwo_support' := begin
      have [ident h] [":", expr «expr ⊆ »({a : Γ | «expr ≠ »(«expr∑ in , »((ij : «expr × »(Γ, Γ)), add_antidiagonal x.is_pwo_support y.is_pwo_support a, «expr * »(x.coeff ij.fst, y.coeff ij.snd)), 0)}, {a : Γ | (add_antidiagonal x.is_pwo_support y.is_pwo_support a).nonempty})] [],
      { intros [ident a, ident ha],
        contrapose ["!"] [ident ha],
        simp [] [] [] ["[", expr not_nonempty_iff_eq_empty.1 ha, "]"] [] [] },
      exact [expr is_pwo_support_add_antidiagonal.mono h]
    end } }

@[simp]
theorem mul_coeff [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} :
  (x*y).coeff a = ∑ij in add_antidiagonal x.is_pwo_support y.is_pwo_support a, x.coeff ij.fst*y.coeff ij.snd :=
  rfl

theorem mul_coeff_right' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ} (hs : s.is_pwo)
  (hys : y.support ⊆ s) :
  (x*y).coeff a = ∑ij in add_antidiagonal x.is_pwo_support hs a, x.coeff ij.fst*y.coeff ij.snd :=
  by 
    rw [mul_coeff]
    apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_right hys) _ fun _ _ => rfl 
    intro b hb 
    simp only [not_and, not_not, mem_sdiff, mem_add_antidiagonal, Ne.def, Set.mem_set_of_eq, mem_support] at hb 
    rw [hb.2 hb.1.1 hb.1.2.1, mul_zero]

theorem mul_coeff_left' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ} (hs : s.is_pwo)
  (hxs : x.support ⊆ s) :
  (x*y).coeff a = ∑ij in add_antidiagonal hs y.is_pwo_support a, x.coeff ij.fst*y.coeff ij.snd :=
  by 
    rw [mul_coeff]
    apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_left hxs) _ fun _ _ => rfl 
    intro b hb 
    simp only [not_and, not_not, mem_sdiff, mem_add_antidiagonal, Ne.def, Set.mem_set_of_eq, mem_support] at hb 
    rw [not_not.1 fun con => hb.1.2.2 (hb.2 hb.1.1 Con), zero_mul]

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance [non_unital_non_assoc_semiring R] : distrib (hahn_series Γ R) :=
{ left_distrib := λ x y z, begin
    ext [] [ident a] [],
    have [ident hwf] [] [":=", expr y.is_pwo_support.union z.is_pwo_support],
    rw ["[", expr mul_coeff_right' hwf, ",", expr add_coeff, ",", expr mul_coeff_right' hwf (set.subset_union_right _ _), ",", expr mul_coeff_right' hwf (set.subset_union_left _ _), "]"] [],
    { simp [] [] ["only"] ["[", expr add_coeff, ",", expr mul_add, ",", expr sum_add_distrib, "]"] [] [] },
    { intro [ident b],
      simp [] [] ["only"] ["[", expr add_coeff, ",", expr ne.def, ",", expr set.mem_union_eq, ",", expr set.mem_set_of_eq, ",", expr mem_support, "]"] [] [],
      contrapose ["!"] [],
      intro [ident h],
      rw ["[", expr h.1, ",", expr h.2, ",", expr add_zero, "]"] [] }
  end,
  right_distrib := λ x y z, begin
    ext [] [ident a] [],
    have [ident hwf] [] [":=", expr x.is_pwo_support.union y.is_pwo_support],
    rw ["[", expr mul_coeff_left' hwf, ",", expr add_coeff, ",", expr mul_coeff_left' hwf (set.subset_union_right _ _), ",", expr mul_coeff_left' hwf (set.subset_union_left _ _), "]"] [],
    { simp [] [] ["only"] ["[", expr add_coeff, ",", expr add_mul, ",", expr sum_add_distrib, "]"] [] [] },
    { intro [ident b],
      simp [] [] ["only"] ["[", expr add_coeff, ",", expr ne.def, ",", expr set.mem_union_eq, ",", expr set.mem_set_of_eq, ",", expr mem_support, "]"] [] [],
      contrapose ["!"] [],
      intro [ident h],
      rw ["[", expr h.1, ",", expr h.2, ",", expr add_zero, "]"] [] }
  end,
  ..hahn_series.has_mul,
  ..hahn_series.has_add }

theorem single_mul_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} {b : Γ} :
  (single b r*x).coeff (a+b) = r*x.coeff a :=
  by 
    byCases' hr : r = 0
    ·
      simp [hr]
    simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
    byCases' hx : x.coeff a = 0
    ·
      simp only [hx, mul_zero]
      rw [sum_congr _ fun _ _ => rfl, sum_empty]
      ext ⟨a1, a2⟩
      simp only [not_mem_empty, not_and, Set.mem_singleton_iff, not_not, mem_add_antidiagonal, Set.mem_set_of_eq,
        iff_falseₓ]
      rintro h1 rfl h2 
      rw [add_commₓ] at h1 
      rw [←add_right_cancelₓ h1] at hx 
      exact h2 hx 
    trans ∑ij : Γ × Γ in {(b, a)}, (single b r).coeff ij.fst*x.coeff ij.snd
    ·
      apply sum_congr _ fun _ _ => rfl 
      ext ⟨a1, a2⟩
      simp only [Set.mem_singleton_iff, Prod.mk.inj_iffₓ, mem_add_antidiagonal, mem_singleton, Set.mem_set_of_eq]
      split 
      ·
        rintro ⟨h1, rfl, h2⟩
        rw [add_commₓ] at h1 
        refine' ⟨rfl, add_right_cancelₓ h1⟩
      ·
        rintro ⟨rfl, rfl⟩
        refine' ⟨add_commₓ _ _, _⟩
        simp [hx]
    ·
      simp 

theorem mul_single_coeff_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} {b : Γ} :
  (x*single b r).coeff (a+b) = x.coeff a*r :=
  by 
    byCases' hr : r = 0
    ·
      simp [hr]
    simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, Ne.def, not_false_iff, smul_eq_mul]
    byCases' hx : x.coeff a = 0
    ·
      simp only [hx, zero_mul]
      rw [sum_congr _ fun _ _ => rfl, sum_empty]
      ext ⟨a1, a2⟩
      simp only [not_mem_empty, not_and, Set.mem_singleton_iff, not_not, mem_add_antidiagonal, Set.mem_set_of_eq,
        iff_falseₓ]
      rintro h1 h2 rfl 
      rw [←add_right_cancelₓ h1] at hx 
      exact h2 hx 
    trans ∑ij : Γ × Γ in {(a, b)}, x.coeff ij.fst*(single b r).coeff ij.snd
    ·
      apply sum_congr _ fun _ _ => rfl 
      ext ⟨a1, a2⟩
      simp only [Set.mem_singleton_iff, Prod.mk.inj_iffₓ, mem_add_antidiagonal, mem_singleton, Set.mem_set_of_eq]
      split 
      ·
        rintro ⟨h1, h2, rfl⟩
        refine' ⟨add_right_cancelₓ h1, rfl⟩
      ·
        rintro ⟨rfl, rfl⟩
        simp [hx]
    ·
      simp 

@[simp]
theorem mul_single_zero_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
  (x*single 0 r).coeff a = x.coeff a*r :=
  by 
    rw [←add_zeroₓ a, mul_single_coeff_add, add_zeroₓ]

theorem single_zero_mul_coeff [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
  (single 0 r*x).coeff a = r*x.coeff a :=
  by 
    rw [←add_zeroₓ a, single_mul_coeff_add, add_zeroₓ]

@[simp]
theorem single_zero_mul_eq_smul [Semiringₓ R] {r : R} {x : HahnSeries Γ R} : (single 0 r*x) = r • x :=
  by 
    ext 
    exact single_zero_mul_coeff

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
  support (x*y) ⊆ support x+support y :=
  by 
    apply Set.Subset.trans (fun x hx => _) support_add_antidiagonal_subset_add
    ·
      exact x.is_pwo_support
    ·
      exact y.is_pwo_support 
    contrapose! hx 
    simp only [not_nonempty_iff_eq_empty, Ne.def, Set.mem_set_of_eq] at hx 
    simp [hx]

theorem mul_coeff_order_add_order {Γ} [LinearOrderedCancelAddCommMonoid Γ] [NonUnitalNonAssocSemiring R]
  {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0) : (x*y).coeff (x.order+y.order) = x.coeff x.order*y.coeff y.order :=
  by 
    rw [order_of_ne hx, order_of_ne hy, mul_coeff, Finset.add_antidiagonal_min_add_min, Finset.sum_singleton]

private theorem mul_assoc' [NonUnitalSemiring R] (x y z : HahnSeries Γ R) : ((x*y)*z) = x*y*z :=
  by 
    ext b 
    rw [mul_coeff_left' (x.is_pwo_support.add y.is_pwo_support) support_mul_subset_add_support,
      mul_coeff_right' (y.is_pwo_support.add z.is_pwo_support) support_mul_subset_add_support]
    simp only [mul_coeff, add_coeff, sum_mul, mul_sum, sum_sigma']
    refine' sum_bij_ne_zero (fun a has ha0 => ⟨⟨a.2.1, a.2.2+a.1.2⟩, ⟨a.2.2, a.1.2⟩⟩) _ _ _ _
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2 
      simp only [true_andₓ, Set.image2_add, eq_self_iff_true, mem_add_antidiagonal, Ne.def, Set.image_prod, mem_sigma,
        Set.mem_set_of_eq] at H1 H2⊢
      obtain ⟨⟨rfl, ⟨H3, nz⟩⟩, ⟨rfl, nx, ny⟩⟩ := H1 
      refine' ⟨⟨(add_assocₓ _ _ _).symm, nx, Set.add_mem_add ny nz⟩, ny, nz⟩
    ·
      rintro ⟨⟨i1, j1⟩, ⟨k1, l1⟩⟩ ⟨⟨i2, j2⟩, ⟨k2, l2⟩⟩ H1 H2 H3 H4 H5 
      simp only [Set.image2_add, Prod.mk.inj_iffₓ, mem_add_antidiagonal, Ne.def, Set.image_prod, mem_sigma,
        Set.mem_set_of_eq, heq_iff_eq] at H1 H3 H5 
      obtain ⟨⟨rfl, H⟩, rfl, rfl⟩ := H5 
      simp only [and_trueₓ, Prod.mk.inj_iffₓ, eq_self_iff_true, heq_iff_eq]
      exact add_right_cancelₓ (H1.1.1.trans H3.1.1.symm)
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2 
      simp only [exists_prop, Set.image2_add, Prod.mk.inj_iffₓ, mem_add_antidiagonal, Sigma.exists, Ne.def,
        Set.image_prod, mem_sigma, Set.mem_set_of_eq, heq_iff_eq, Prod.exists] at H1 H2⊢
      obtain ⟨⟨rfl, nx, H⟩, rfl, ny, nz⟩ := H1 
      exact
        ⟨i+k, l, i, k, ⟨⟨add_assocₓ _ _ _, Set.add_mem_add nx ny, nz⟩, rfl, nx, ny⟩,
          fun con => H2 ((mul_assocₓ _ _ _).symm.trans Con), ⟨rfl, rfl⟩, rfl, rfl⟩
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H1 H2 
      simp [mul_assocₓ]

instance  [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (HahnSeries Γ R) :=
  { HahnSeries.addCommMonoid, HahnSeries.distrib with zero := 0, add := ·+·, mul := ·*·,
    zero_mul :=
      fun _ =>
        by 
          ext 
          simp ,
    mul_zero :=
      fun _ =>
        by 
          ext 
          simp  }

instance  [NonUnitalSemiring R] : NonUnitalSemiring (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocSemiring with zero := 0, add := ·+·, mul := ·*·, mul_assoc := mul_assoc' }

instance  [NonAssocSemiring R] : NonAssocSemiring (HahnSeries Γ R) :=
  { HahnSeries.nonUnitalNonAssocSemiring with zero := 0, one := 1, add := ·+·, mul := ·*·,
    one_mul :=
      fun x =>
        by 
          ext 
          exact single_zero_mul_coeff.trans (one_mulₓ _),
    mul_one :=
      fun x =>
        by 
          ext 
          exact mul_single_zero_coeff.trans (mul_oneₓ _) }

instance  [Semiringₓ R] : Semiringₓ (HahnSeries Γ R) :=
  { HahnSeries.nonAssocSemiring, HahnSeries.nonUnitalSemiring with zero := 0, one := 1, add := ·+·, mul := ·*· }

instance  [CommSemiringₓ R] : CommSemiringₓ (HahnSeries Γ R) :=
  { HahnSeries.semiring with
    mul_comm :=
      fun x y =>
        by 
          ext 
          simpRw [mul_coeff, mul_commₓ]
          refine'
            sum_bij (fun a ha => ⟨a.2, a.1⟩) _
              (fun a ha =>
                by 
                  simp )
              _ _
          ·
            intro a ha 
            simp only [mem_add_antidiagonal, Ne.def, Set.mem_set_of_eq] at ha⊢
            obtain ⟨h1, h2, h3⟩ := ha 
            refine' ⟨_, h3, h2⟩
            rw [add_commₓ, h1]
          ·
            rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb hab 
            rw [Prod.ext_iff] at *
            refine' ⟨hab.2, hab.1⟩
          ·
            intro a ha 
            refine'
              ⟨a.swap, _,
                by 
                  simp ⟩
            simp only [Prod.fst_swap, mem_add_antidiagonal, Prod.snd_swap, Ne.def, Set.mem_set_of_eq] at ha⊢
            exact ⟨(add_commₓ _ _).trans ha.1, ha.2.2, ha.2.1⟩ }

instance  [Ringₓ R] : Ringₓ (HahnSeries Γ R) :=
  { HahnSeries.semiring, HahnSeries.addCommGroup with  }

instance  [CommRingₓ R] : CommRingₓ (HahnSeries Γ R) :=
  { HahnSeries.commSemiring, HahnSeries.ring with  }

instance  {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Ringₓ R] [IsDomain R] : IsDomain (HahnSeries Γ R) :=
  { HahnSeries.nontrivial, HahnSeries.ring with
    eq_zero_or_eq_zero_of_mul_eq_zero :=
      fun x y xy =>
        by 
          byCases' hx : x = 0
          ·
            left 
            exact hx 
          right 
          contrapose! xy 
          rw [HahnSeries.ext_iff, Function.funext_iffₓ, not_forall]
          refine' ⟨x.order+y.order, _⟩
          rw [mul_coeff_order_add_order hx xy, zero_coeff, mul_eq_zero]
          simp [coeff_order_ne_zero, hx, xy] }

@[simp]
theorem order_mul {Γ} [LinearOrderedCancelAddCommMonoid Γ] [Ringₓ R] [IsDomain R] {x y : HahnSeries Γ R} (hx : x ≠ 0)
  (hy : y ≠ 0) : (x*y).order = x.order+y.order :=
  by 
    apply le_antisymmₓ
    ·
      apply order_le_of_coeff_ne_zero 
      rw [mul_coeff_order_add_order hx hy]
      exact mul_ne_zero (coeff_order_ne_zero hx) (coeff_order_ne_zero hy)
    ·
      rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ←Set.IsWf.min_add]
      exact Set.IsWf.min_le_min_of_subset support_mul_subset_add_support

section NonUnitalNonAssocSemiring

variable[NonUnitalNonAssocSemiring R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} : (single a r*single b s) = single (a+b) (r*s) :=
  by 
    ext x 
    byCases' h : x = a+b
    ·
      rw [h, mul_single_coeff_add]
      simp 
    ·
      rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero]
      rintro ⟨y1, y2⟩ hy 
      obtain ⟨rfl, hy1, hy2⟩ := mem_add_antidiagonal.1 hy 
      rw [eq_of_mem_support_single hy1, eq_of_mem_support_single hy2] at h 
      exact (h rfl).elim

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable[NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
def C : R →+* HahnSeries Γ R :=
  { toFun := single 0, map_zero' := single_eq_zero, map_one' := rfl,
    map_add' :=
      fun x y =>
        by 
          ext a 
          byCases' h : a = 0 <;> simp [h],
    map_mul' :=
      fun x y =>
        by 
          rw [single_mul_single, zero_addₓ] }

@[simp]
theorem C_zero : C (0 : R) = (0 : HahnSeries Γ R) :=
  C.map_zero

@[simp]
theorem C_one : C (1 : R) = (1 : HahnSeries Γ R) :=
  C.map_one

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem C_injective : function.injective (C : R → hahn_series Γ R) :=
begin
  intros [ident r, ident s, ident rs],
  rw ["[", expr ext_iff, ",", expr function.funext_iff, "]"] ["at", ident rs],
  have [ident h] [] [":=", expr rs 0],
  rwa ["[", expr C_apply, ",", expr single_coeff_same, ",", expr C_apply, ",", expr single_coeff_same, "]"] ["at", ident h]
end

theorem C_ne_zero {r : R} (h : r ≠ 0) : (C r : HahnSeries Γ R) ≠ 0 :=
  by 
    contrapose! h 
    rw [←C_zero] at h 
    exact C_injective h

theorem order_C {r : R} : order (C r : HahnSeries Γ R) = 0 :=
  by 
    byCases' h : r = 0
    ·
      rw [h, C_zero, order_zero]
    ·
      exact order_single h

end NonAssocSemiring

section Semiringₓ

variable[Semiringₓ R]

theorem C_mul_eq_smul {r : R} {x : HahnSeries Γ R} : (C r*x) = r • x :=
  single_zero_mul_eq_smul

end Semiringₓ

section Domain

variable{Γ' : Type _}[OrderedCancelAddCommMonoid Γ']

theorem emb_domain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ') (hf : ∀ x y, f (x+y) = f x+f y)
  (x y : HahnSeries Γ R) : emb_domain f (x*y) = emb_domain f x*emb_domain f y :=
  by 
    ext g 
    byCases' hg : g ∈ Set.Range f
    ·
      obtain ⟨g, rfl⟩ := hg 
      simp only [mul_coeff, emb_domain_coeff]
      trans
        ∑ij in
          (add_antidiagonal x.is_pwo_support y.is_pwo_support g).map
            (Function.Embedding.prodMap f.to_embedding f.to_embedding),
          (emb_domain f x).coeff ij.1*(emb_domain f y).coeff ij.2
      ·
        simp 
      apply sum_subset
      ·
        rintro ⟨i, j⟩ hij 
        simp only [exists_prop, mem_map, Prod.mk.inj_iffₓ, mem_add_antidiagonal, Ne.def,
          Function.Embedding.coe_prod_map, mem_support, Prod.exists] at hij 
        obtain ⟨i, j, ⟨rfl, hx, hy⟩, rfl, rfl⟩ := hij 
        simp [hx, hy, hf]
      ·
        rintro ⟨_, _⟩ h1 h2 
        contrapose! h2 
        obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).1
        obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).2
        simp only [exists_prop, mem_map, Prod.mk.inj_iffₓ, mem_add_antidiagonal, Ne.def,
          Function.Embedding.coe_prod_map, mem_support, Prod.exists]
        simp only [mem_add_antidiagonal, emb_domain_coeff, Ne.def, mem_support, ←hf] at h1 
        exact ⟨i, j, ⟨f.injective h1.1, h1.2⟩, rfl⟩
    ·
      rw [emb_domain_notin_range hg, eq_comm]
      contrapose! hg 
      obtain ⟨_, _, hi, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
      obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset hi 
      obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset hj 
      refine' ⟨i+j, hf i j⟩

theorem emb_domain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
  emb_domain f (1 : HahnSeries Γ R) = (1 : HahnSeries Γ' R) :=
  emb_domain_single.trans$ hf.symm ▸ rfl

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
def emb_domain_ring_hom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)
  (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ R →+* HahnSeries Γ' R :=
  { toFun := emb_domain ⟨⟨f, hfi⟩, hf⟩, map_one' := emb_domain_one _ f.map_zero, map_mul' := emb_domain_mul _ f.map_add,
    map_zero' := emb_domain_zero, map_add' := emb_domain_add _ }

theorem emb_domain_ring_hom_C [NonAssocSemiring R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
  {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : emb_domain_ring_hom f hfi hf (C r) = C r :=
  emb_domain_single.trans
    (by 
      simp )

end Domain

section Algebra

variable[CommSemiringₓ R]{A : Type _}[Semiringₓ A][Algebra R A]

instance  : Algebra R (HahnSeries Γ A) :=
  { toRingHom := C.comp (algebraMap R A),
    smul_def' :=
      fun r x =>
        by 
          ext 
          simp ,
    commutes' :=
      fun r x =>
        by 
          ext 
          simp only [smul_coeff, single_zero_mul_eq_smul, RingHom.coe_comp, RingHom.to_fun_eq_coe, C_apply,
            Function.comp_app, algebra_map_smul, mul_single_zero_coeff]
          rw [←Algebra.commutes, Algebra.smul_def] }

theorem C_eq_algebra_map : C = algebraMap R (HahnSeries Γ R) :=
  rfl

theorem algebra_map_apply {r : R} : algebraMap R (HahnSeries Γ A) r = C (algebraMap R A r) :=
  rfl

instance  [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R (HahnSeries Γ R)) :=
  ⟨⟨⊥, ⊤,
      by 
        rw [Ne.def, SetLike.ext_iff, not_forall]
        obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
        refine' ⟨single a 1, _⟩
        simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_trueₓ, Algebra.mem_top]
        intro x 
        rw [ext_iff, Function.funext_iffₓ, not_forall]
        refine' ⟨a, _⟩
        rw [single_coeff_same, algebra_map_apply, C_apply, single_coeff_of_ne ha]
        exact zero_ne_one⟩⟩

section Domain

variable{Γ' : Type _}[OrderedCancelAddCommMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps]
def emb_domain_alg_hom (f : Γ →+ Γ') (hfi : Function.Injective f) (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') :
  HahnSeries Γ A →ₐ[R] HahnSeries Γ' A :=
  { emb_domain_ring_hom f hfi hf with commutes' := fun r => emb_domain_ring_hom_C }

end Domain

end Algebra

end Multiplication

section Semiringₓ

variable[Semiringₓ R]

/-- The ring `hahn_series ℕ R` is isomorphic to `power_series R`. -/
@[simps]
def to_power_series : HahnSeries ℕ R ≃+* PowerSeries R :=
  { toFun := fun f => PowerSeries.mk f.coeff,
    invFun := fun f => ⟨fun n => PowerSeries.coeff R n f, (Nat.lt_wf.IsWf _).IsPwo⟩,
    left_inv :=
      fun f =>
        by 
          ext 
          simp ,
    right_inv :=
      fun f =>
        by 
          ext 
          simp ,
    map_add' :=
      fun f g =>
        by 
          ext 
          simp ,
    map_mul' :=
      fun f g =>
        by 
          ext n 
          simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, mul_coeff, is_pwo_support]
          classical 
          refine' sum_filter_ne_zero.symm.trans ((sum_congr _ fun _ _ => rfl).trans sum_filter_ne_zero)
          ext m 
          simp only [nat.mem_antidiagonal, And.congr_left_iff, mem_add_antidiagonal, Ne.def, and_iff_left_iff_imp,
            mem_filter, mem_support]
          intro h1 h2 
          contrapose h1 
          rw [←Decidable.or_iff_not_and_not] at h1 
          cases h1 <;> simp [h1] }

theorem coeff_to_power_series {f : HahnSeries ℕ R} {n : ℕ} : PowerSeries.coeff R n f.to_power_series = f.coeff n :=
  PowerSeries.coeff_mk _ _

theorem coeff_to_power_series_symm {f : PowerSeries R} {n : ℕ} :
  (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff R n f :=
  rfl

variable(Γ)(R)[OrderedSemiring Γ][Nontrivial Γ]

/-- Casts a power series as a Hahn series with coefficients from an `ordered_semiring`. -/
def of_power_series : PowerSeries R →+* HahnSeries Γ R :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strict_mono_cast.Injective fun _ _ => Nat.cast_le).comp
    (RingEquiv.toRingHom to_power_series.symm)

variable{Γ}{R}

theorem of_power_series_injective : Function.Injective (of_power_series Γ R) :=
  emb_domain_injective.comp to_power_series.symm.Injective

@[simp]
theorem of_power_series_apply (x : PowerSeries R) :
  of_power_series Γ R x =
    HahnSeries.embDomain
      ⟨⟨(coeₓ : ℕ → Γ), Nat.strict_mono_cast.Injective⟩,
        fun a b =>
          by 
            simp only [Function.Embedding.coe_fn_mk]
            exact Nat.cast_le⟩
      (to_power_series.symm x) :=
  rfl

theorem of_power_series_apply_coeff (x : PowerSeries R) (n : ℕ) :
  (of_power_series Γ R x).coeff n = PowerSeries.coeff R n x :=
  by 
    simp 

end Semiringₓ

section Algebra

variable(R)[CommSemiringₓ R]{A : Type _}[Semiringₓ A][Algebra R A]

/-- The `R`-algebra `hahn_series ℕ A` is isomorphic to `power_series A`. -/
@[simps]
def to_power_series_alg : HahnSeries ℕ A ≃ₐ[R] PowerSeries A :=
  { to_power_series with
    commutes' :=
      fun r =>
        by 
          ext n 
          simp only [algebra_map_apply, PowerSeries.algebra_map_apply, RingEquiv.to_fun_eq_coe, C_apply,
            coeff_to_power_series]
          cases n
          ·
            simp only [PowerSeries.coeff_zero_eq_constant_coeff, single_coeff_same]
            rfl
          ·
            simp only [n.succ_ne_zero, Ne.def, not_false_iff, single_coeff_of_ne]
            rw [PowerSeries.coeff_C, if_neg n.succ_ne_zero] }

variable(Γ)(R)[OrderedSemiring Γ][Nontrivial Γ]

/-- Casting a power series as a Hahn series with coefficients from an `ordered_semiring`
  is an algebra homomorphism. -/
@[simps]
def of_power_series_alg : PowerSeries A →ₐ[R] HahnSeries Γ A :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strict_mono_cast.Injective fun _ _ => Nat.cast_le).comp
    (AlgEquiv.toAlgHom (to_power_series_alg R).symm)

end Algebra

section Valuation

variable[LinearOrderedAddCommGroup Γ][Ringₓ R][IsDomain R]

instance  : LinearOrderedCommGroup (Multiplicative Γ) :=
  { (inferInstance : LinearOrderₓ (Multiplicative Γ)), (inferInstance : OrderedCommGroup (Multiplicative Γ)) with  }

instance  : LinearOrderedCommGroupWithZero (WithZero (Multiplicative Γ)) :=
  { WithZero.orderedCommMonoid, (inferInstance : LinearOrderₓ (WithZero (Multiplicative Γ))),
    (inferInstance : CommGroupWithZero (WithZero (Multiplicative Γ))) with zero_le_one := WithZero.zero_le 1 }

variable(Γ)(R)

/-- The additive valuation on `hahn_series Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def add_val : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of (fun x => if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order) (if_pos rfl)
    ((if_neg one_ne_zero).trans
      (by 
        simp [order_of_ne]))
    (fun x y =>
      by 
        byCases' hx : x = 0
        ·
          byCases' hy : y = 0 <;>
            ·
              simp [hx, hy]
        ·
          byCases' hy : y = 0
          ·
            simp [hx, hy]
          ·
            simp only [hx, hy, support_nonempty_iff, if_neg, not_false_iff, is_wf_support]
            byCases' hxy : (x+y) = 0
            ·
              simp [hxy]
            rw [if_neg hxy, ←WithTop.coe_min, WithTop.coe_le_coe]
            exact min_order_le_order_add hx hy hxy)
    fun x y =>
      by 
        byCases' hx : x = 0
        ·
          simp [hx]
        byCases' hy : y = 0
        ·
          simp [hy]
        rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ←WithTop.coe_add, WithTop.coe_eq_coe, order_mul hx hy]

variable{Γ}{R}

theorem add_val_apply {x : HahnSeries Γ R} :
  add_val Γ R x = if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order :=
  AddValuation.of_apply _

@[simp]
theorem add_val_apply_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : add_val Γ R x = x.order :=
  if_neg hx

theorem add_val_le_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : add_val Γ R x ≤ g :=
  by 
    rw [add_val_apply_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
    exact order_le_of_coeff_ne_zero h

end Valuation

theorem is_pwo_Union_support_powers [LinearOrderedAddCommGroup Γ] [Ringₓ R] [IsDomain R] {x : HahnSeries Γ R}
  (hx : 0 < add_val Γ R x) : (⋃n : ℕ, (x^n).Support).IsPwo :=
  by 
    apply (x.is_wf_support.is_pwo.add_submonoid_closure fun g hg => _).mono _
    ·
      exact WithTop.coe_le_coe.1 (le_transₓ (le_of_ltₓ hx) (add_val_le_of_coeff_ne_zero hg))
    refine' Set.Union_subset fun n => _ 
    induction' n with n ih <;> intro g hn
    ·
      simp only [exists_prop, and_trueₓ, Set.mem_singleton_iff, Set.set_of_eq_eq_singleton, mem_support,
        ite_eq_right_iff, Ne.def, not_false_iff, one_ne_zero, pow_zeroₓ, not_forall, one_coeff] at hn 
      rw [hn, SetLike.mem_coe]
      exact AddSubmonoid.zero_mem _
    ·
      obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn 
      exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hi) (ih hj))

section 

variable(Γ)(R)[PartialOrderₓ Γ][AddCommMonoidₓ R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure summable_family(α : Type _) where 
  toFun : α → HahnSeries Γ R 
  is_pwo_Union_support' : Set.IsPwo (⋃a : α, (to_fun a).Support)
  finite_co_support' : ∀ g : Γ, { a | (to_fun a).coeff g ≠ 0 }.Finite

end 

namespace SummableFamily

section AddCommMonoidₓ

variable[PartialOrderₓ Γ][AddCommMonoidₓ R]{α : Type _}

instance  : CoeFun (summable_family Γ R α) fun _ => α → HahnSeries Γ R :=
  ⟨to_fun⟩

theorem is_pwo_Union_support (s : summable_family Γ R α) : Set.IsPwo (⋃a : α, (s a).Support) :=
  s.is_pwo_Union_support'

theorem finite_co_support (s : summable_family Γ R α) (g : Γ) : (Function.Support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g

theorem coe_injective : @Function.Injective (summable_family Γ R α) (α → HahnSeries Γ R) coeFn
| ⟨f1, hU1, hf1⟩, ⟨f2, hU2, hf2⟩, h =>
  by 
    change f1 = f2 at h 
    subst h

@[ext]
theorem ext {s t : summable_family Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  coe_injective$ funext h

instance  : Add (summable_family Γ R α) :=
  ⟨fun x y =>
      { toFun := x+y,
        is_pwo_Union_support' :=
          (x.is_pwo_Union_support.union y.is_pwo_Union_support).mono
            (by 
              rw [←Set.Union_union_distrib]
              exact Set.Union_subset_Union fun a => support_add_subset),
        finite_co_support' :=
          fun g =>
            ((x.finite_co_support g).union (y.finite_co_support g)).Subset
              (by 
                intro a ha 
                change ((x a).coeff g+(y a).coeff g) ≠ 0 at ha 
                rw [Set.mem_union, Function.mem_support, Function.mem_support]
                contrapose! ha 
                rw [ha.1, ha.2, add_zeroₓ]) }⟩

instance  : HasZero (summable_family Γ R α) :=
  ⟨⟨0,
      by 
        simp ,
      by 
        simp ⟩⟩

instance  : Inhabited (summable_family Γ R α) :=
  ⟨0⟩

@[simp]
theorem coe_add {s t : summable_family Γ R α} : «expr⇑ » (s+t) = s+t :=
  rfl

theorem add_apply {s t : summable_family Γ R α} {a : α} : (s+t) a = s a+t a :=
  rfl

@[simp]
theorem coe_zero : ((0 : summable_family Γ R α) : α → HahnSeries Γ R) = 0 :=
  rfl

theorem zero_apply {a : α} : (0 : summable_family Γ R α) a = 0 :=
  rfl

instance  : AddCommMonoidₓ (summable_family Γ R α) :=
  { add := ·+·, zero := 0,
    zero_add :=
      fun s =>
        by 
          ext 
          apply zero_addₓ,
    add_zero :=
      fun s =>
        by 
          ext 
          apply add_zeroₓ,
    add_comm :=
      fun s t =>
        by 
          ext 
          apply add_commₓ,
    add_assoc :=
      fun r s t =>
        by 
          ext 
          apply add_assocₓ }

/-- The infinite sum of a `summable_family` of Hahn series. -/
def hsum (s : summable_family Γ R α) : HahnSeries Γ R :=
  { coeff := fun g => ∑ᶠi, (s i).coeff g,
    is_pwo_support' :=
      s.is_pwo_Union_support.mono
        fun g =>
          by 
            contrapose 
            rw [Set.mem_Union, not_exists, Function.mem_support, not_not]
            simpRw [mem_support, not_not]
            intro h 
            rw [finsum_congr h, finsum_zero] }

@[simp]
theorem hsum_coeff {s : summable_family Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠi, (s i).coeff g :=
  rfl

theorem support_hsum_subset {s : summable_family Γ R α} : s.hsum.support ⊆ ⋃a : α, (s a).Support :=
  fun g hg =>
    by 
      rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg 
      obtain ⟨a, h1, h2⟩ := exists_ne_zero_of_sum_ne_zero hg 
      rw [Set.mem_Union]
      exact ⟨a, h2⟩

@[simp]
theorem hsum_add {s t : summable_family Γ R α} : (s+t).hsum = s.hsum+t.hsum :=
  by 
    ext g 
    simp only [hsum_coeff, add_coeff, add_apply]
    exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

end AddCommMonoidₓ

section AddCommGroupₓ

variable[PartialOrderₓ Γ][AddCommGroupₓ R]{α : Type _}{s t : summable_family Γ R α}{a : α}

instance  : AddCommGroupₓ (summable_family Γ R α) :=
  { summable_family.add_comm_monoid with
    neg :=
      fun s =>
        { toFun := fun a => -s a,
          is_pwo_Union_support' :=
            by 
              simpRw [support_neg]
              exact s.is_pwo_Union_support',
          finite_co_support' :=
            fun g =>
              by 
                simp only [neg_coeff', Pi.neg_apply, Ne.def, neg_eq_zero]
                exact s.finite_co_support g },
    add_left_neg :=
      fun a =>
        by 
          ext 
          apply add_left_negₓ }

@[simp]
theorem coe_neg : «expr⇑ » (-s) = -s :=
  rfl

theorem neg_apply : (-s) a = -s a :=
  rfl

@[simp]
theorem coe_sub : «expr⇑ » (s - t) = s - t :=
  rfl

theorem sub_apply : (s - t) a = s a - t a :=
  rfl

end AddCommGroupₓ

section Semiringₓ

variable[OrderedCancelAddCommMonoid Γ][Semiringₓ R]{α : Type _}

instance  : HasScalar (HahnSeries Γ R) (summable_family Γ R α) :=
  { smul :=
      fun x s =>
        { toFun := fun a => x*s a,
          is_pwo_Union_support' :=
            by 
              apply (x.is_pwo_support.add s.is_pwo_Union_support).mono 
              refine' Set.Subset.trans (Set.Union_subset_Union fun a => support_mul_subset_add_support) _ 
              intro g 
              simp only [Set.mem_Union, exists_imp_distrib]
              exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_Union _ a)) ha,
          finite_co_support' :=
            fun g =>
              by 
                refine'
                  ((add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g).finite_to_set.bUnion
                        fun ij hij => _).Subset
                    fun a ha => _
                ·
                  exact fun ij hij => Function.Support fun a => (s a).coeff ij.2
                ·
                  apply s.finite_co_support
                ·
                  obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support ha 
                  simp only [exists_prop, Set.mem_Union, mem_add_antidiagonal, mul_coeff, Ne.def, mem_support,
                    is_pwo_support, Prod.exists]
                  refine' ⟨i, j, mem_coe.2 (mem_add_antidiagonal.2 ⟨rfl, hi, Set.mem_Union.2 ⟨a, hj⟩⟩), hj⟩ } }

@[simp]
theorem smul_apply {x : HahnSeries Γ R} {s : summable_family Γ R α} {a : α} : (x • s) a = x*s a :=
  rfl

instance  : Module (HahnSeries Γ R) (summable_family Γ R α) :=
  { smul := · • ·, smul_zero := fun x => ext fun a => mul_zero _, zero_smul := fun x => ext fun a => zero_mul _,
    one_smul := fun x => ext fun a => one_mulₓ _, add_smul := fun x y s => ext fun a => add_mulₓ _ _ _,
    smul_add := fun x s t => ext fun a => mul_addₓ _ _ _, mul_smul := fun x y s => ext fun a => mul_assocₓ _ _ _ }

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem hsum_smul
{x : hahn_series Γ R}
{s : summable_family Γ R α} : «expr = »(«expr • »(x, s).hsum, «expr * »(x, s.hsum)) :=
begin
  ext [] [ident g] [],
  simp [] [] ["only"] ["[", expr mul_coeff, ",", expr hsum_coeff, ",", expr smul_apply, "]"] [] [],
  have [ident h] [":", expr ∀
   i, «expr ⊆ »((s i).support, «expr⋃ , »((j), (s j).support))] [":=", expr set.subset_Union _],
  refine [expr (eq.trans (finsum_congr (λ
      a, _)) (finsum_sum_comm (add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g) (λ
      i ij, «expr * »(x.coeff (prod.fst ij), (s i).coeff ij.snd)) _)).trans _],
  { refine [expr sum_subset (add_antidiagonal_mono_right (set.subset_Union _ a)) _],
    rintro ["⟨", ident i, ",", ident j, "⟩", ident hU, ident ha],
    rw [expr mem_add_antidiagonal] ["at", "*"],
    rw ["[", expr not_not.1 (λ con, ha ⟨hU.1, hU.2.1, con⟩), ",", expr mul_zero, "]"] [] },
  { rintro ["⟨", ident i, ",", ident j, "⟩", ident hij],
    refine [expr (s.finite_co_support j).subset _],
    simp_rw ["[", expr function.support_subset_iff', ",", expr function.mem_support, ",", expr not_not, "]"] [],
    intros [ident a, ident ha],
    rw ["[", expr ha, ",", expr mul_zero, "]"] [] },
  { refine [expr (sum_congr rfl _).trans (sum_subset (add_antidiagonal_mono_right _) _).symm],
    { rintro ["⟨", ident i, ",", ident j, "⟩", ident hij],
      rw [expr mul_finsum] [],
      apply [expr s.finite_co_support] },
    { intros [ident x, ident hx],
      simp [] [] ["only"] ["[", expr set.mem_Union, ",", expr ne.def, ",", expr mem_support, "]"] [] [],
      contrapose ["!"] [ident hx],
      simp [] [] [] ["[", expr hx, "]"] [] [] },
    { rintro ["⟨", ident i, ",", ident j, "⟩", ident hU, ident ha],
      rw [expr mem_add_antidiagonal] ["at", "*"],
      rw ["[", "<-", expr hsum_coeff, ",", expr not_not.1 (λ
        con, ha ⟨hU.1, hU.2.1, con⟩), ",", expr mul_zero, "]"] [] } }
end

/-- The summation of a `summable_family` as a `linear_map`. -/
@[simps]
def lsum : summable_family Γ R α →ₗ[HahnSeries Γ R] HahnSeries Γ R :=
  { toFun := hsum, map_add' := fun _ _ => hsum_add, map_smul' := fun _ _ => hsum_smul }

@[simp]
theorem hsum_sub {R : Type _} [Ringₓ R] {s t : summable_family Γ R α} : (s - t).hsum = s.hsum - t.hsum :=
  by 
    rw [←lsum_apply, LinearMap.map_sub, lsum_apply, lsum_apply]

end Semiringₓ

section OfFinsupp

variable[PartialOrderₓ Γ][AddCommMonoidₓ R]{α : Type _}

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family with only finitely many nonzero elements is summable. -/
def of_finsupp (f : «expr →₀ »(α, hahn_series Γ R)) : summable_family Γ R α :=
{ to_fun := f,
  is_pwo_Union_support' := begin
    apply [expr (f.support.is_pwo_sup (λ a, (f a).support) (λ a ha, (f a).is_pwo_support)).mono],
    intros [ident g, ident hg],
    obtain ["⟨", ident a, ",", ident ha, "⟩", ":=", expr set.mem_Union.1 hg],
    have [ident haf] [":", expr «expr ∈ »(a, f.support)] [],
    { rw [expr finsupp.mem_support_iff] [],
      contrapose ["!"] [ident ha],
      rw ["[", expr ha, ",", expr support_zero, "]"] [],
      exact [expr set.not_mem_empty _] },
    have [ident h] [":", expr «expr ≤ »(λ i, (f i).support a, _)] [":=", expr le_sup haf],
    exact [expr h ha]
  end,
  finite_co_support' := λ g, begin
    refine [expr f.support.finite_to_set.subset (λ a ha, _)],
    simp [] [] ["only"] ["[", expr coeff.add_monoid_hom_apply, ",", expr mem_coe, ",", expr finsupp.mem_support_iff, ",", expr ne.def, ",", expr function.mem_support, "]"] [] [],
    contrapose ["!"] [ident ha],
    simp [] [] [] ["[", expr ha, "]"] [] []
  end }

@[simp]
theorem coe_of_finsupp {f : α →₀ HahnSeries Γ R} : «expr⇑ » (summable_family.of_finsupp f) = f :=
  rfl

@[simp]
theorem hsum_of_finsupp {f : α →₀ HahnSeries Γ R} : (of_finsupp f).hsum = f.sum fun a => id :=
  by 
    ext g 
    simp only [hsum_coeff, coe_of_finsupp, Finsupp.sum, Ne.def]
    simpRw [←coeff.add_monoid_hom_apply, id.def]
    rw [AddMonoidHom.map_sum, finsum_eq_sum_of_support_subset]
    intro x h 
    simp only [coeff.add_monoid_hom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def]
    contrapose! h 
    simp [h]

end OfFinsupp

section EmbDomain

variable[PartialOrderₓ Γ][AddCommMonoidₓ R]{α β : Type _}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def emb_domain (s : summable_family Γ R α) (f : α ↪ β) : summable_family Γ R β :=
  { toFun := fun b => if h : b ∈ Set.Range f then s (Classical.some h) else 0,
    is_pwo_Union_support' :=
      by 
        refine' s.is_pwo_Union_support.mono (Set.Union_subset fun b g h => _)
        byCases' hb : b ∈ Set.Range f
        ·
          rw [dif_pos hb] at h 
          exact Set.mem_Union.2 ⟨Classical.some hb, h⟩
        ·
          contrapose! h 
          simp [hb],
    finite_co_support' :=
      fun g =>
        ((s.finite_co_support g).Image f).Subset
          (by 
            intro b h 
            byCases' hb : b ∈ Set.Range f
            ·
              simp only [Ne.def, Set.mem_set_of_eq, dif_pos hb] at h 
              exact ⟨Classical.some hb, h, Classical.some_spec hb⟩
            ·
              contrapose! h 
              simp only [Ne.def, Set.mem_set_of_eq, dif_neg hb, not_not, zero_coeff]) }

variable(s : summable_family Γ R α)(f : α ↪ β){a : α}{b : β}

theorem emb_domain_apply : s.emb_domain f b = if h : b ∈ Set.Range f then s (Classical.some h) else 0 :=
  rfl

@[simp]
theorem emb_domain_image : s.emb_domain f (f a) = s a :=
  by 
    rw [emb_domain_apply, dif_pos (Set.mem_range_self a)]
    exact congr rfl (f.injective (Classical.some_spec (Set.mem_range_self a)))

@[simp]
theorem emb_domain_notin_range (h : b ∉ Set.Range f) : s.emb_domain f b = 0 :=
  by 
    rw [emb_domain_apply, dif_neg h]

@[simp]
theorem hsum_emb_domain : (s.emb_domain f).hsum = s.hsum :=
  by 
    ext g 
    simp only [hsum_coeff, emb_domain_apply, apply_dite HahnSeries.coeff, dite_apply, zero_coeff]
    exact finsum_emb_domain f fun a => (s a).coeff g

end EmbDomain

section Powers

variable[LinearOrderedAddCommGroup Γ][CommRingₓ R][IsDomain R]

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The powers of an element of positive valuation form a summable family. -/
def powers (x : hahn_series Γ R) (hx : «expr < »(0, add_val Γ R x)) : summable_family Γ R exprℕ() :=
{ to_fun := λ n, «expr ^ »(x, n),
  is_pwo_Union_support' := is_pwo_Union_support_powers hx,
  finite_co_support' := λ g, begin
    have [ident hpwo] [] [":=", expr is_pwo_Union_support_powers hx],
    by_cases [expr hg, ":", expr «expr ∈ »(g, «expr⋃ , »((n : exprℕ()), {g | «expr ≠ »(«expr ^ »(x, n).coeff g, 0)}))],
    swap,
    { exact [expr set.finite_empty.subset (λ n hn, hg (set.mem_Union.2 ⟨n, hn⟩))] },
    apply [expr hpwo.is_wf.induction hg],
    intros [ident y, ident ys, ident hy],
    refine [expr ((((add_antidiagonal x.is_pwo_support hpwo y).finite_to_set.bUnion (λ
         ij hij, hy ij.snd _ _)).image nat.succ).union (set.finite_singleton 0)).subset _],
    { exact [expr (mem_add_antidiagonal.1 (mem_coe.1 hij)).2.2] },
    { obtain ["⟨", ident rfl, ",", ident hi, ",", ident hj, "⟩", ":=", expr mem_add_antidiagonal.1 (mem_coe.1 hij)],
      rw ["[", "<-", expr zero_add ij.snd, ",", "<-", expr add_assoc, ",", expr add_zero, "]"] [],
      exact [expr add_lt_add_right (with_top.coe_lt_coe.1 (lt_of_lt_of_le hx (add_val_le_of_coeff_ne_zero hi))) _] },
    { intros [ident n, ident hn],
      cases [expr n] [],
      { exact [expr set.mem_union_right _ (set.mem_singleton 0)] },
      { obtain ["⟨", ident i, ",", ident j, ",", ident hi, ",", ident hj, ",", ident rfl, "⟩", ":=", expr support_mul_subset_add_support hn],
        refine [expr set.mem_union_left _ ⟨n, set.mem_Union.2 ⟨⟨i, j⟩, set.mem_Union.2 ⟨_, hj⟩⟩, rfl⟩],
        simp [] [] ["only"] ["[", expr true_and, ",", expr set.mem_Union, ",", expr mem_add_antidiagonal, ",", expr mem_coe, ",", expr eq_self_iff_true, ",", expr ne.def, ",", expr mem_support, ",", expr set.mem_set_of_eq, "]"] [] [],
        exact [expr ⟨hi, ⟨n, hj⟩⟩] } }
  end }

variable{x : HahnSeries Γ R}(hx : 0 < add_val Γ R x)

@[simp]
theorem coe_powers : «expr⇑ » (powers x hx) = pow x :=
  rfl

theorem emb_domain_succ_smul_powers :
  (x • powers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ = powers x hx - of_finsupp (Finsupp.single 0 1) :=
  by 
    apply summable_family.ext fun n => _ 
    cases n
    ·
      rw [emb_domain_notin_range, sub_apply, coe_powers, pow_zeroₓ, coe_of_finsupp, Finsupp.single_eq_same, sub_self]
      rw [Set.mem_range, not_exists]
      exact Nat.succ_ne_zero
    ·
      refine' Eq.trans (emb_domain_image _ ⟨Nat.succ, Nat.succ_injective⟩) _ 
      simp only [pow_succₓ, coe_powers, coe_sub, smul_apply, coe_of_finsupp, Pi.sub_apply]
      rw [Finsupp.single_eq_of_ne n.succ_ne_zero.symm, sub_zero]

theorem one_sub_self_mul_hsum_powers : ((1 - x)*(powers x hx).hsum) = 1 :=
  by 
    rw [←hsum_smul, sub_smul, one_smul, hsum_sub, ←hsum_emb_domain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩,
      emb_domain_succ_smul_powers]
    simp 

end Powers

end SummableFamily

section Inversion

variable[LinearOrderedAddCommGroup Γ]

section IsDomain

variable[CommRingₓ R][IsDomain R]

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unit_aux
(x : hahn_series Γ R)
{r : R}
(hr : «expr = »(«expr * »(r, x.coeff x.order), 1)) : «expr < »(0, add_val Γ R «expr - »(1, «expr * »(«expr * »(C r, single «expr- »(x.order) 1), x))) :=
begin
  have [ident h10] [":", expr «expr ≠ »((1 : R), 0)] [":=", expr one_ne_zero],
  have [ident x0] [":", expr «expr ≠ »(x, 0)] [":=", expr ne_zero_of_coeff_ne_zero (right_ne_zero_of_mul_eq_one hr)],
  refine [expr lt_of_le_of_ne ((add_val Γ R).map_le_sub (ge_of_eq (add_val Γ R).map_one) _) _],
  { simp [] [] ["only"] ["[", expr add_valuation.map_mul, "]"] [] [],
    rw ["[", expr add_val_apply_of_ne x0, ",", expr add_val_apply_of_ne (single_ne_zero h10), ",", expr add_val_apply_of_ne _, ",", expr order_C, ",", expr order_single h10, ",", expr with_top.coe_zero, ",", expr zero_add, ",", "<-", expr with_top.coe_add, ",", expr neg_add_self, ",", expr with_top.coe_zero, "]"] [],
    { exact [expr le_refl 0] },
    { exact [expr C_ne_zero (left_ne_zero_of_mul_eq_one hr)] } },
  { rw ["[", expr add_val_apply, ",", "<-", expr with_top.coe_zero, "]"] [],
    split_ifs [] [],
    { apply [expr with_top.coe_ne_top] },
    rw ["[", expr ne.def, ",", expr with_top.coe_eq_coe, "]"] [],
    intro [ident con],
    apply [expr coeff_order_ne_zero h],
    rw ["[", "<-", expr con, ",", expr mul_assoc, ",", expr sub_coeff, ",", expr one_coeff, ",", expr if_pos rfl, ",", expr C_mul_eq_smul, ",", expr smul_coeff, ",", expr smul_eq_mul, ",", "<-", expr add_neg_self x.order, ",", expr single_mul_coeff_add, ",", expr one_mul, ",", expr hr, ",", expr sub_self, "]"] [] }
end

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_unit_iff {x : hahn_series Γ R} : «expr ↔ »(is_unit x, is_unit (x.coeff x.order)) :=
begin
  split,
  { rintro ["⟨", "⟨", ident u, ",", ident i, ",", ident ui, ",", ident iu, "⟩", ",", ident rfl, "⟩"],
    refine [expr is_unit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order) ((mul_coeff_order_add_order (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui)).symm.trans _)],
    rw ["[", expr ui, ",", expr one_coeff, ",", expr if_pos, "]"] [],
    rw ["[", "<-", expr order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ",", expr ui, ",", expr order_one, "]"] [] },
  { rintro ["⟨", "⟨", ident u, ",", ident i, ",", ident ui, ",", ident iu, "⟩", ",", ident h, "⟩"],
    rw ["[", expr units.coe_mk, "]"] ["at", ident h],
    rw [expr h] ["at", ident iu],
    have [ident h] [] [":=", expr summable_family.one_sub_self_mul_hsum_powers (unit_aux x iu)],
    rw ["[", expr sub_sub_cancel, "]"] ["at", ident h],
    exact [expr is_unit_of_mul_is_unit_right (is_unit_of_mul_eq_one _ _ h)] }
end

end IsDomain

-- error in RingTheory.HahnSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance [field R] : field (hahn_series Γ R) :=
{ inv := λ
  x, if x0 : «expr = »(x, 0) then 0 else «expr * »(«expr * »(C «expr ⁻¹»(x.coeff x.order), single «expr- »(x.order) 1), (summable_family.powers _ (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum),
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ x x0, begin
    refine [expr (congr rfl (dif_neg x0)).trans _],
    have [ident h] [] [":=", expr summable_family.one_sub_self_mul_hsum_powers (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))],
    rw ["[", expr sub_sub_cancel, "]"] ["at", ident h],
    rw ["[", "<-", expr mul_assoc, ",", expr mul_comm x, ",", expr h, "]"] []
  end,
  ..hahn_series.is_domain,
  ..hahn_series.comm_ring }

end Inversion

end HahnSeries

