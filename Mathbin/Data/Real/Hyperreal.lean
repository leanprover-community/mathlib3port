import Mathbin.Order.Filter.FilterProduct 
import Mathbin.Analysis.SpecificLimits

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/


open Filter Filter.Germ

open_locale TopologicalSpace Classical

-- error in Data.Real.Hyperreal: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler linear_ordered_field
/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
@[derive #["[", expr linear_ordered_field, ",", expr inhabited, "]"]]
def hyperreal : Type :=
germ (hyperfilter exprℕ() : filter exprℕ()) exprℝ()

namespace Hyperreal

notation "ℝ*" => Hyperreal

noncomputable instance : CoeTₓ ℝ ℝ* :=
  ⟨fun x => («expr↑ » x : germ _ _)⟩

@[simp, normCast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  germ.const_inj

@[simp, normCast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp, normCast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe

@[simp, normCast]
theorem coe_one : «expr↑ » (1 : ℝ) = (1 : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_zero : «expr↑ » (0 : ℝ) = (0 : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_inv (x : ℝ) : «expr↑ » (x⁻¹) = (x⁻¹ : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_neg (x : ℝ) : «expr↑ » (-x) = (-x : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_add (x y : ℝ) : «expr↑ » (x+y) = (x+y : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_bit0 (x : ℝ) : «expr↑ » (bit0 x) = (bit0 x : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_bit1 (x : ℝ) : «expr↑ » (bit1 x) = (bit1 x : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_mul (x y : ℝ) : «expr↑ » (x*y) = (x*y : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_div (x y : ℝ) : «expr↑ » (x / y) = (x / y : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_sub (x y : ℝ) : «expr↑ » (x - y) = (x - y : ℝ*) :=
  rfl

@[simp, normCast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  germ.const_lt

@[simp, normCast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe

@[simp, normCast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  germ.const_le_iff

@[simp, normCast]
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |x| :=
  by 
    convert const_abs x 
    apply lattice_of_linear_order_eq_filter_germ_lattice

@[simp, normCast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max x y :=
  germ.const_max _ _

@[simp, normCast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min x y :=
  germ.const_min _ _

/-- Construct a hyperreal number from a sequence of real numbers. -/
noncomputable def of_seq (f : ℕ → ℝ) : ℝ* :=
  («expr↑ » f : germ (hyperfilter ℕ : Filter ℕ) ℝ)

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* :=
  of_seq$ fun n => n⁻¹

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* :=
  of_seq coeₓ

localized [Hyperreal] notation "ε" => Hyperreal.epsilon

localized [Hyperreal] notation "ω" => Hyperreal.omega

theorem epsilon_eq_inv_omega : ε = ω⁻¹ :=
  rfl

theorem inv_epsilon_eq_omega : ε⁻¹ = ω :=
  @inv_inv₀ _ _ ω

theorem epsilon_pos : 0 < ε :=
  suffices ∀ᶠi in hyperfilter ℕ, (0 : ℝ) < (i : ℕ)⁻¹by 
    rwa [lt_def]
  have h0' : { n:ℕ | ¬0 < n } = {0} :=
    by 
      simp only [not_ltₓ, Set.set_of_eq_eq_singleton.symm] <;> ext <;> exact Nat.le_zero_iff 
  by 
    simp only [inv_pos, Nat.cast_pos]
    exact
      mem_hyperfilter_of_finite_compl
        (by 
          convert Set.finite_singleton _)

theorem epsilon_ne_zero : ε ≠ 0 :=
  ne_of_gtₓ epsilon_pos

theorem omega_pos : 0 < ω :=
  by 
    rw [←inv_epsilon_eq_omega] <;> exact inv_pos.2 epsilon_pos

theorem omega_ne_zero : ω ≠ 0 :=
  ne_of_gtₓ omega_pos

theorem epsilon_mul_omega : (ε*ω) = 1 :=
  @inv_mul_cancel _ _ ω omega_ne_zero

-- error in Data.Real.Hyperreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_of_tendsto_zero_of_pos
{f : exprℕ() → exprℝ()}
(hf : tendsto f at_top (expr𝓝() 0)) : ∀ {r : exprℝ()}, «expr < »(0, r) → «expr < »(of_seq f, (r : «exprℝ*»())) :=
begin
  simp [] [] ["only"] ["[", expr metric.tendsto_at_top, ",", expr dist_zero_right, ",", expr norm, ",", expr lt_def, "]"] [] ["at", ident hf, "⊢"],
  intros [ident r, ident hr],
  cases [expr hf r hr] ["with", ident N, ident hf'],
  have [ident hs] [":", expr «expr ⊆ »(«expr ᶜ»({i : exprℕ() | «expr < »(f i, r)}), {i : exprℕ() | «expr ≤ »(i, N)})] [":=", expr λ
   i
   hi1, le_of_lt (by simp [] [] ["only"] ["[", expr lt_iff_not_ge, "]"] [] []; exact [expr λ
    hi2, hi1 (lt_of_le_of_lt (le_abs_self _) (hf' i hi2))] : «expr < »(i, N))],
  exact [expr mem_hyperfilter_of_finite_compl ((set.finite_le_nat N).subset hs)]
end

theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : tendsto f at_top (𝓝 0)) :
  ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < of_seq f :=
  fun r hr =>
    have hg := hf.neg 
    neg_lt_of_neg_lt
      (by 
        rw [neg_zero] at hg <;> exact lt_of_tendsto_zero_of_pos hg hr)

theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : tendsto f at_top (𝓝 0)) : ∀ {r : ℝ}, r < 0 → (r : ℝ*) < of_seq f :=
  fun r hr =>
    by 
      rw [←neg_negₓ r, coe_neg] <;> exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

theorem epsilon_lt_pos (x : ℝ) : 0 < x → ε < x :=
  lt_of_tendsto_zero_of_pos tendsto_inverse_at_top_nhds_0_nat

/-- Standard part predicate -/
def is_st (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r+δ

/-- Standard part function: like a "round" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ :=
  fun x => if h : ∃ r, is_st x r then Classical.some h else 0

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def infinitesimal (x : ℝ*) :=
  is_st x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def infinite_pos (x : ℝ*) :=
  ∀ r : ℝ, «expr↑ » r < x

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def infinite_neg (x : ℝ*) :=
  ∀ r : ℝ, x < r

/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def Infinite (x : ℝ*) :=
  infinite_pos x ∨ infinite_neg x

/-!
### Some facts about `st`
-/


private theorem is_st_unique' (x : ℝ*) (r s : ℝ) (hr : is_st x r) (hs : is_st x s) (hrs : r < s) : False :=
  have hrs' := half_pos$ sub_pos_of_lt hrs 
  have hr' := (hr _ hrs').2
  have hs' := (hs _ hrs').1
  have h : s - (s - r) / 2 = r+(s - r) / 2 :=
    by 
      linarith 
  by 
    normCast  at *
    rw [h] at hs' 
    exact not_lt_of_lt hs' hr'

theorem is_st_unique {x : ℝ*} {r s : ℝ} (hr : is_st x r) (hs : is_st x s) : r = s :=
  by 
    rcases lt_trichotomyₓ r s with (h | h | h)
    ·
      exact False.elim (is_st_unique' x r s hr hs h)
    ·
      exact h
    ·
      exact False.elim (is_st_unique' x s r hs hr h)

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, is_st x r) → ¬Infinite x :=
  fun he hi =>
    Exists.dcases_on he$
      fun r hr =>
        hi.elim (fun hip => not_lt_of_lt (hr 2 zero_lt_two).2 (hip$ r+2))
          fun hin => not_lt_of_lt (hr 2 zero_lt_two).1 (hin$ r - 2)

theorem is_st_Sup {x : ℝ*} (hni : ¬Infinite x) : is_st x (Sup { y:ℝ | (y : ℝ*) < x }) :=
  let S : Set ℝ := { y:ℝ | (y : ℝ*) < x }
  let R : _ := Sup S 
  have hnile := not_forall.mp (not_or_distrib.mp hni).1
  have hnige := not_forall.mp (not_or_distrib.mp hni).2 
  Exists.dcases_on hnile$
    Exists.dcases_on hnige$
      fun r₁ hr₁ r₂ hr₂ =>
        have HR₁ : S.nonempty := ⟨r₁ - 1, lt_of_lt_of_leₓ (coe_lt_coe.2$ sub_one_lt _) (not_ltₓ.mp hr₁)⟩
        have HR₂ : BddAbove S := ⟨r₂, fun y hy => le_of_ltₓ (coe_lt_coe.1 (lt_of_lt_of_leₓ hy (not_ltₓ.mp hr₂)))⟩
        fun δ hδ =>
          ⟨lt_of_not_ge'$
              fun c =>
                have hc : ∀ y _ : y ∈ S, y ≤ R - δ := fun y hy => coe_le_coe.1$ le_of_ltₓ$ lt_of_lt_of_leₓ hy c 
                not_lt_of_le (cSup_le HR₁ hc)$ sub_lt_self R hδ,
            lt_of_not_ge'$
              fun c =>
                have hc : «expr↑ » (R+δ / 2) < x :=
                  lt_of_lt_of_leₓ (add_lt_add_left (coe_lt_coe.2 (half_lt_self hδ)) R) c 
                not_lt_of_le (le_cSup HR₂ hc)$ (lt_add_iff_pos_right _).mpr$ half_pos hδ⟩

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, is_st x r :=
  ⟨Sup { y:ℝ | (y : ℝ*) < x }, is_st_Sup hni⟩

theorem st_eq_Sup {x : ℝ*} : st x = Sup { y:ℝ | (y : ℝ*) < x } :=
  by 
    unfold st 
    splitIfs
    ·
      exact is_st_unique (Classical.some_spec h) (is_st_Sup (not_infinite_of_exists_st h))
    ·
      cases' not_imp_comm.mp exists_st_of_not_infinite h with H H
      ·
        rw [(Set.ext fun i => ⟨fun hi => Set.mem_univ i, fun hi => H i⟩ : { y:ℝ | (y : ℝ*) < x } = Set.Univ)]
        exact real.Sup_univ.symm
      ·
        rw
          [(Set.ext
            fun i => ⟨fun hi => False.elim (not_lt_of_lt (H i) hi), fun hi => False.elim (Set.not_mem_empty i hi)⟩ :
          { y:ℝ | (y : ℝ*) < x } = ∅)]
        exact real.Sup_empty.symm

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, is_st x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, is_st x r :=
  iff_not_comm.mp exists_st_iff_not_infinite

theorem st_infinite {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  by 
    unfold st 
    splitIfs
    ·
      exact False.elim ((infinite_iff_not_exists_st.mp hi) h)
    ·
      rfl

theorem st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : st x = r :=
  by 
    unfold st 
    splitIfs
    ·
      exact is_st_unique (Classical.some_spec h) hxr
    ·
      exact False.elim (h ⟨r, hxr⟩)

theorem is_st_st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st x (st x) :=
  by 
    rwa [st_of_is_st hxr]

theorem is_st_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, is_st x r) : is_st x (st x) :=
  Exists.dcases_on hx fun r => is_st_st_of_is_st

theorem is_st_st {x : ℝ*} (hx : st x ≠ 0) : is_st x (st x) :=
  by 
    unfold st 
    splitIfs
    ·
      exact Classical.some_spec h
    ·
      exact
        False.elim
          (hx
            (by 
              unfold st <;> splitIfs <;> rfl))

theorem is_st_st' {x : ℝ*} (hx : ¬Infinite x) : is_st x (st x) :=
  is_st_st_of_exists_st$ exists_st_of_not_infinite hx

theorem is_st_refl_real (r : ℝ) : is_st r r :=
  fun δ hδ => ⟨sub_lt_self _ (coe_lt_coe.2 hδ), lt_add_of_pos_right _ (coe_lt_coe.2 hδ)⟩

theorem st_id_real (r : ℝ) : st r = r :=
  st_of_is_st (is_st_refl_real r)

theorem eq_of_is_st_real {r s : ℝ} : is_st r s → r = s :=
  is_st_unique (is_st_refl_real r)

theorem is_st_real_iff_eq {r s : ℝ} : is_st r s ↔ r = s :=
  ⟨eq_of_is_st_real,
    fun hrs =>
      by 
        rw [hrs] <;> exact is_st_refl_real s⟩

theorem is_st_symm_real {r s : ℝ} : is_st r s ↔ is_st s r :=
  by 
    rw [is_st_real_iff_eq, is_st_real_iff_eq, eq_comm]

theorem is_st_trans_real {r s t : ℝ} : is_st r s → is_st s t → is_st r t :=
  by 
    rw [is_st_real_iff_eq, is_st_real_iff_eq, is_st_real_iff_eq] <;> exact Eq.trans

theorem is_st_inj_real {r₁ r₂ s : ℝ} (h1 : is_st r₁ s) (h2 : is_st r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_is_st_real h1) (eq_of_is_st_real h2).symm

theorem is_st_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : is_st x r ↔ ∀ δ : ℝ, 0 < δ → |x - r| < δ :=
  by 
    simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, is_st, and_comm, add_commₓ]

theorem is_st_add {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x+y) (r+s) :=
  fun hxr hys d hd =>
    have hxr' := hxr (d / 2) (half_pos hd)
    have hys' := hys (d / 2) (half_pos hd)
    ⟨by 
        convert add_lt_add hxr'.1 hys'.1 using 1 <;> normCast <;> linarith,
      by 
        convert add_lt_add hxr'.2 hys'.2 using 1 <;> normCast <;> linarith⟩

theorem is_st_neg {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st (-x) (-r) :=
  fun d hd =>
    show -(r : ℝ*) - d < -x ∧ -x < (-r)+d by 
      cases hxr d hd <;> split  <;> linarith

theorem is_st_sub {x y : ℝ*} {r s : ℝ} : is_st x r → is_st y s → is_st (x - y) (r - s) :=
  fun hxr hys =>
    by 
      rw [sub_eq_add_neg, sub_eq_add_neg] <;> exact is_st_add hxr (is_st_neg hys)

theorem lt_of_is_st_lt {x y : ℝ*} {r s : ℝ} (hxr : is_st x r) (hys : is_st y s) : r < s → x < y :=
  fun hrs =>
    have hrs' : 0 < (s - r) / 2 := half_pos (sub_pos.mpr hrs)
    have hxr' := (hxr _ hrs').2
    have hys' := (hys _ hrs').1
    have H1 : (r+(s - r) / 2) = (r+s) / 2 :=
      by 
        linarith 
    have H2 : s - (s - r) / 2 = (r+s) / 2 :=
      by 
        linarith 
    by 
      normCast  at *
      rw [H1] at hxr' 
      rw [H2] at hys' 
      exact lt_transₓ hxr' hys'

theorem is_st_le_of_le {x y : ℝ*} {r s : ℝ} (hrx : is_st x r) (hsy : is_st y s) : x ≤ y → r ≤ s :=
  by 
    rw [←not_ltₓ, ←not_ltₓ, not_imp_not] <;> exact lt_of_is_st_lt hsy hrx

theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  have hx' := is_st_st' hix 
  have hy' := is_st_st' hiy 
  is_st_le_of_le hx' hy'

theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  have hx' := is_st_st' hix 
  have hy' := is_st_st' hiy 
  lt_of_is_st_lt hx' hy'

/-!
### Basic lemmas about infinite
-/


theorem infinite_pos_def {x : ℝ*} : infinite_pos x ↔ ∀ r : ℝ, «expr↑ » r < x :=
  by 
    rw [iff_eq_eq] <;> rfl

theorem infinite_neg_def {x : ℝ*} : infinite_neg x ↔ ∀ r : ℝ, x < r :=
  by 
    rw [iff_eq_eq] <;> rfl

theorem ne_zero_of_infinite {x : ℝ*} : Infinite x → x ≠ 0 :=
  fun hI h0 =>
    Or.cases_on hI
      (fun hip =>
        lt_irreflₓ (0 : ℝ*)
          ((by 
              rwa [←h0] :
            infinite_pos 0)
            0))
      fun hin =>
        lt_irreflₓ (0 : ℝ*)
          ((by 
              rwa [←h0] :
            infinite_neg 0)
            0)

theorem not_infinite_zero : ¬Infinite 0 :=
  fun hI => ne_zero_of_infinite hI rfl

theorem pos_of_infinite_pos {x : ℝ*} : infinite_pos x → 0 < x :=
  fun hip => hip 0

theorem neg_of_infinite_neg {x : ℝ*} : infinite_neg x → x < 0 :=
  fun hin => hin 0

theorem not_infinite_pos_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬infinite_pos x :=
  fun hn hp => not_lt_of_lt (hn 1) (hp 1)

theorem not_infinite_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬infinite_neg x :=
  imp_not_comm.mp not_infinite_pos_of_infinite_neg

theorem infinite_neg_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → infinite_neg (-x) :=
  fun hp r => neg_lt.mp (hp (-r))

theorem infinite_pos_neg_of_infinite_neg {x : ℝ*} : infinite_neg x → infinite_pos (-x) :=
  fun hp r => lt_neg.mp (hp (-r))

theorem infinite_pos_iff_infinite_neg_neg {x : ℝ*} : infinite_pos x ↔ infinite_neg (-x) :=
  ⟨infinite_neg_neg_of_infinite_pos, fun hin => neg_negₓ x ▸ infinite_pos_neg_of_infinite_neg hin⟩

theorem infinite_neg_iff_infinite_pos_neg {x : ℝ*} : infinite_neg x ↔ infinite_pos (-x) :=
  ⟨infinite_pos_neg_of_infinite_neg, fun hin => neg_negₓ x ▸ infinite_neg_neg_of_infinite_pos hin⟩

theorem infinite_iff_infinite_neg {x : ℝ*} : Infinite x ↔ Infinite (-x) :=
  ⟨fun hi =>
      Or.cases_on hi (fun hip => Or.inr (infinite_neg_neg_of_infinite_pos hip))
        fun hin => Or.inl (infinite_pos_neg_of_infinite_neg hin),
    fun hi =>
      Or.cases_on hi (fun hipn => Or.inr (infinite_neg_iff_infinite_pos_neg.mpr hipn))
        fun hinp => Or.inl (infinite_pos_iff_infinite_neg_neg.mpr hinp)⟩

theorem not_infinite_of_infinitesimal {x : ℝ*} : infinitesimal x → ¬Infinite x :=
  fun hi hI =>
    have hi' := hi 2 zero_lt_two 
    Or.dcases_on hI
      (fun hip =>
        have hip' := hip 2
        not_lt_of_lt hip'
          (by 
            convert hi'.2 <;> exact (zero_addₓ 2).symm))
      fun hin =>
        have hin' := hin (-2)
        not_lt_of_lt hin'
          (by 
            convert hi'.1 <;> exact (zero_sub 2).symm)

theorem not_infinitesimal_of_infinite {x : ℝ*} : Infinite x → ¬infinitesimal x :=
  imp_not_comm.mp not_infinite_of_infinitesimal

theorem not_infinitesimal_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬infinitesimal x :=
  fun hp => not_infinitesimal_of_infinite (Or.inl hp)

theorem not_infinitesimal_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬infinitesimal x :=
  fun hn => not_infinitesimal_of_infinite (Or.inr hn)

theorem infinite_pos_iff_infinite_and_pos {x : ℝ*} : infinite_pos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩,
    fun ⟨hi, hp⟩ => hi.cases_on (fun hip => hip) fun hin => False.elim (not_lt_of_lt hp (hin 0))⟩

theorem infinite_neg_iff_infinite_and_neg {x : ℝ*} : infinite_neg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩,
    fun ⟨hi, hp⟩ => hi.cases_on (fun hin => False.elim (not_lt_of_lt hp (hin 0))) fun hip => hip⟩

theorem infinite_pos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : infinite_pos x ↔ Infinite x :=
  by 
    rw [infinite_pos_iff_infinite_and_pos] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hp⟩⟩

theorem infinite_pos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : infinite_pos x ↔ Infinite x :=
  Or.cases_on (lt_or_eq_of_leₓ hp) infinite_pos_iff_infinite_of_pos
    fun h =>
      by 
        rw [h.symm] <;>
          exact ⟨fun hIP => False.elim (not_infinite_zero (Or.inl hIP)), fun hI => False.elim (not_infinite_zero hI)⟩

theorem infinite_neg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : infinite_neg x ↔ Infinite x :=
  by 
    rw [infinite_neg_iff_infinite_and_neg] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hn⟩⟩

theorem infinite_pos_abs_iff_infinite_abs {x : ℝ*} : infinite_pos |x| ↔ Infinite |x| :=
  infinite_pos_iff_infinite_of_nonneg (abs_nonneg _)

theorem infinite_iff_infinite_pos_abs {x : ℝ*} : Infinite x ↔ infinite_pos |x| :=
  ⟨fun hi d =>
      Or.cases_on hi
        (fun hip =>
          by 
            rw [abs_of_pos (hip 0)] <;> exact hip d)
        fun hin =>
          by 
            rw [abs_of_neg (hin 0)] <;> exact lt_neg.mp (hin (-d)),
    fun hipa =>
      by 
        rcases lt_trichotomyₓ x 0 with (h | h | h)
        ·
          exact
            Or.inr
              (infinite_neg_iff_infinite_pos_neg.mpr
                (by 
                  rwa [abs_of_neg h] at hipa))
        ·
          exact
            False.elim
              (ne_zero_of_infinite
                (Or.inl
                  (by 
                    rw [h] <;> rwa [h, abs_zero] at hipa))
                h)
        ·
          exact
            Or.inl
              (by 
                rwa [abs_of_pos h] at hipa)⟩

theorem infinite_iff_infinite_abs {x : ℝ*} : Infinite x ↔ Infinite |x| :=
  by 
    rw [←infinite_pos_iff_infinite_of_nonneg (abs_nonneg _), infinite_iff_infinite_pos_abs]

theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  ⟨fun hI r => coe_abs r ▸ infinite_iff_infinite_pos_abs.mp hI |r|,
    fun hR =>
      Or.cases_on (max_choice x (-x)) (fun h => Or.inl$ fun r => lt_of_le_of_ltₓ (le_abs_self _) (h ▸ hR r))
        fun h => Or.inr$ fun r => neg_lt_neg_iff.mp$ lt_of_le_of_ltₓ (neg_le_abs_self _) (h ▸ hR r)⟩

theorem infinite_pos_add_not_infinite_neg {x y : ℝ*} : infinite_pos x → ¬infinite_neg y → infinite_pos (x+y) :=
  by 
    intro hip hnin r 
    cases' not_forall.mp hnin with r₂ hr₂ 
    convert add_lt_add_of_lt_of_le (hip (r+-r₂)) (not_lt.mp hr₂) using 1
    simp 

theorem not_infinite_neg_add_infinite_pos {x y : ℝ*} : ¬infinite_neg x → infinite_pos y → infinite_pos (x+y) :=
  fun hx hy =>
    by 
      rw [add_commₓ] <;> exact infinite_pos_add_not_infinite_neg hy hx

theorem infinite_neg_add_not_infinite_pos {x y : ℝ*} : infinite_neg x → ¬infinite_pos y → infinite_neg (x+y) :=
  by 
    rw [@infinite_neg_iff_infinite_pos_neg x, @infinite_pos_iff_infinite_neg_neg y,
        @infinite_neg_iff_infinite_pos_neg (x+y), neg_add] <;>
      exact infinite_pos_add_not_infinite_neg

theorem not_infinite_pos_add_infinite_neg {x y : ℝ*} : ¬infinite_pos x → infinite_neg y → infinite_neg (x+y) :=
  fun hx hy =>
    by 
      rw [add_commₓ] <;> exact infinite_neg_add_not_infinite_pos hy hx

theorem infinite_pos_add_infinite_pos {x y : ℝ*} : infinite_pos x → infinite_pos y → infinite_pos (x+y) :=
  fun hx hy => infinite_pos_add_not_infinite_neg hx (not_infinite_neg_of_infinite_pos hy)

theorem infinite_neg_add_infinite_neg {x y : ℝ*} : infinite_neg x → infinite_neg y → infinite_neg (x+y) :=
  fun hx hy => infinite_neg_add_not_infinite_pos hx (not_infinite_pos_of_infinite_neg hy)

theorem infinite_pos_add_not_infinite {x y : ℝ*} : infinite_pos x → ¬Infinite y → infinite_pos (x+y) :=
  fun hx hy => infinite_pos_add_not_infinite_neg hx (not_or_distrib.mp hy).2

theorem infinite_neg_add_not_infinite {x y : ℝ*} : infinite_neg x → ¬Infinite y → infinite_neg (x+y) :=
  fun hx hy => infinite_neg_add_not_infinite_pos hx (not_or_distrib.mp hy).1

theorem infinite_pos_of_tendsto_top {f : ℕ → ℝ} (hf : tendsto f at_top at_top) : infinite_pos (of_seq f) :=
  fun r =>
    have hf' := tendsto_at_top_at_top.mp hf 
    Exists.cases_on (hf' (r+1))$
      fun i hi =>
        have hi' : ∀ a : ℕ, (f a < r+1) → a < i :=
          fun a =>
            by 
              rw [←not_leₓ, ←not_leₓ] <;> exact not_imp_not.mpr (hi a)
        have hS : «expr ᶜ» { a:ℕ | r < f a } ⊆ { a:ℕ | a ≤ i } :=
          by 
            simp only [Set.compl_set_of, not_ltₓ] <;>
              exact fun a har => le_of_ltₓ (hi' a (lt_of_le_of_ltₓ har (lt_add_one _)))
        germ.coe_lt.2$ mem_hyperfilter_of_finite_compl$ (Set.finite_le_nat _).Subset hS

theorem infinite_neg_of_tendsto_bot {f : ℕ → ℝ} (hf : tendsto f at_top at_bot) : infinite_neg (of_seq f) :=
  fun r =>
    have hf' := tendsto_at_top_at_bot.mp hf 
    Exists.cases_on (hf' (r - 1))$
      fun i hi =>
        have hi' : ∀ a : ℕ, r - 1 < f a → a < i :=
          fun a =>
            by 
              rw [←not_leₓ, ←not_leₓ] <;> exact not_imp_not.mpr (hi a)
        have hS : «expr ᶜ» { a:ℕ | f a < r } ⊆ { a:ℕ | a ≤ i } :=
          by 
            simp only [Set.compl_set_of, not_ltₓ] <;>
              exact fun a har => le_of_ltₓ (hi' a (lt_of_lt_of_leₓ (sub_one_lt _) har))
        germ.coe_lt.2$ mem_hyperfilter_of_finite_compl$ (Set.finite_le_nat _).Subset hS

theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) :=
  not_imp_not.mpr infinite_iff_infinite_neg.mpr

theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x+y) :=
  have hx' := exists_st_of_not_infinite hx 
  have hy' := exists_st_of_not_infinite hy 
  Exists.cases_on hx'$ Exists.cases_on hy'$ fun r hr s hs => not_infinite_of_exists_st$ ⟨s+r, is_st_add hs hr⟩

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni =>
      Exists.dcases_on (not_forall.mp (not_or_distrib.mp hni).1)$
        Exists.dcases_on (not_forall.mp (not_or_distrib.mp hni).2)$
          fun r hr s hs =>
            by 
              rw [not_ltₓ] at hr hs <;>
                exact
                  ⟨r - 1, s+1,
                    ⟨lt_of_lt_of_leₓ
                        (by 
                          rw [sub_eq_add_neg] <;> normNum)
                        hr,
                      lt_of_le_of_ltₓ hs
                        (by 
                          normNum)⟩⟩,
    fun hrs =>
      Exists.dcases_on hrs$
        fun r hr =>
          Exists.dcases_on hr$
            fun s hs => not_or_distrib.mpr ⟨not_forall.mpr ⟨s, lt_asymmₓ hs.2⟩, not_forall.mpr ⟨r, lt_asymmₓ hs.1⟩⟩⟩

theorem not_infinite_real (r : ℝ) : ¬Infinite r :=
  by 
    rw [not_infinite_iff_exist_lt_gt] <;> exact ⟨r - 1, r+1, coe_lt_coe.2$ sub_one_lt r, coe_lt_coe.2$ lt_add_one r⟩

theorem not_real_of_infinite {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r :=
  fun hi r hr => not_infinite_real r$ @Eq.subst _ Infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/


-- error in Data.Real.Hyperreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem is_st_mul'
{x y : «exprℝ*»()}
{r s : exprℝ()}
(hxr : is_st x r)
(hys : is_st y s)
(hs : «expr ≠ »(s, 0)) : is_st «expr * »(x, y) «expr * »(r, s) :=
have hxr' : _ := is_st_iff_abs_sub_lt_delta.mp hxr,
have hys' : _ := is_st_iff_abs_sub_lt_delta.mp hys,
have h : _ := «expr $ »(not_infinite_iff_exist_lt_gt.mp, «expr $ »(not_imp_not.mpr infinite_iff_infinite_abs.mpr, not_infinite_of_exists_st ⟨r, hxr⟩)),
«expr $ »(Exists.cases_on h, λ
 u
 h', «expr $ »(Exists.cases_on h', λ
  (t)
  ⟨hu, ht⟩, «expr $ »(is_st_iff_abs_sub_lt_delta.mpr, λ d hd, calc
     «expr = »(«expr| |»(«expr - »(«expr * »(x, y), «expr * »(r, s))), «expr| |»(«expr + »(«expr * »(x, «expr - »(y, s)), «expr * »(«expr - »(x, r), s)))) : by rw ["[", expr mul_sub, ",", expr sub_mul, ",", expr add_sub, ",", expr sub_add_cancel, "]"] []
     «expr ≤ »(..., «expr + »(«expr| |»(«expr * »(x, «expr - »(y, s))), «expr| |»(«expr * »(«expr - »(x, r), s)))) : abs_add _ _
     «expr ≤ »(..., «expr + »(«expr * »(«expr| |»(x), «expr| |»(«expr - »(y, s))), «expr * »(«expr| |»(«expr - »(x, r)), «expr| |»(s)))) : by simp [] [] ["only"] ["[", expr abs_mul, "]"] [] []
     «expr ≤ »(..., «expr + »(«expr * »(«expr| |»(x), («expr / »(«expr / »(d, t), 2) : exprℝ())), «expr * »((«expr / »(«expr / »(d, «expr| |»(s)), 2) : exprℝ()), «expr| |»(s)))) : add_le_add «expr $ »(mul_le_mul_of_nonneg_left «expr $ »(le_of_lt, «expr $ »(hys' _, «expr $ »(half_pos, «expr $ »(div_pos hd, «expr $ »(coe_pos.1, lt_of_le_of_lt (abs_nonneg x) ht))))), abs_nonneg _) «expr $ »(mul_le_mul_of_nonneg_right «expr $ »(le_of_lt, «expr $ »(hxr' _, «expr $ »(half_pos, «expr $ »(div_pos hd, abs_pos.2 hs)))), abs_nonneg _)
     «expr = »(..., («expr + »(«expr * »(«expr / »(d, 2), «expr / »(«expr| |»(x), t)), «expr / »(d, 2)) : «exprℝ*»())) : by { push_cast ["[", "-", ident filter.germ.const_div, "]"] [],
       have [] [":", expr «expr ≠ »((«expr| |»(s) : «exprℝ*»()), 0)] [],
       by simpa [] [] [] [] [] [],
       have [] [":", expr «expr ≠ »((2 : «exprℝ*»()), 0)] [":=", expr two_ne_zero],
       field_simp [] ["[", "*", ",", expr add_mul, ",", expr mul_add, ",", expr mul_assoc, ",", expr mul_comm, ",", expr mul_left_comm, "]"] [] [] }
     «expr < »(..., («expr + »(«expr * »(«expr / »(d, 2), 1), «expr / »(d, 2)) : «exprℝ*»())) : add_lt_add_right «expr $ »(mul_lt_mul_of_pos_left («expr $ »(div_lt_one, lt_of_le_of_lt (abs_nonneg x) ht).mpr ht), «expr $ »(half_pos, coe_pos.2 hd)) _
     «expr = »(..., (d : «exprℝ*»())) : by rw ["[", expr mul_one, ",", expr add_halves, "]"] [])))

-- error in Data.Real.Hyperreal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_st_mul
{x y : «exprℝ*»()}
{r s : exprℝ()}
(hxr : is_st x r)
(hys : is_st y s) : is_st «expr * »(x, y) «expr * »(r, s) :=
have h : _ := «expr $ »(not_infinite_iff_exist_lt_gt.mp, «expr $ »(not_imp_not.mpr infinite_iff_infinite_abs.mpr, not_infinite_of_exists_st ⟨r, hxr⟩)),
«expr $ »(Exists.cases_on h, λ
 u
 h', «expr $ »(Exists.cases_on h', λ (t) ⟨hu, ht⟩, begin
    by_cases [expr hs, ":", expr «expr = »(s, 0)],
    { apply [expr is_st_iff_abs_sub_lt_delta.mpr],
      intros [ident d, ident hd],
      have [ident hys'] [":", expr _] [":=", expr is_st_iff_abs_sub_lt_delta.mp hys «expr / »(d, t) (div_pos hd (coe_pos.1 (lt_of_le_of_lt (abs_nonneg x) ht)))],
      rw ["[", expr hs, ",", expr coe_zero, ",", expr sub_zero, "]"] ["at", ident hys'],
      rw ["[", expr hs, ",", expr mul_zero, ",", expr coe_zero, ",", expr sub_zero, ",", expr abs_mul, ",", expr mul_comm, ",", "<-", expr div_mul_cancel (d : «exprℝ*»()) (ne_of_gt (lt_of_le_of_lt (abs_nonneg x) ht)), ",", "<-", expr coe_div, "]"] [],
      exact [expr mul_lt_mul'' hys' ht (abs_nonneg _) (abs_nonneg _)] },
    exact [expr is_st_mul' hxr hys hs]
  end))

theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x*y) :=
  have hx' := exists_st_of_not_infinite hx 
  have hy' := exists_st_of_not_infinite hy 
  Exists.cases_on hx'$ Exists.cases_on hy'$ fun r hr s hs => not_infinite_of_exists_st$ ⟨s*r, is_st_mul hs hr⟩

theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x+y) = st x+st y :=
  have hx' := is_st_st' hx 
  have hy' := is_st_st' hy 
  have hxy := is_st_st' (not_infinite_add hx hy)
  have hxy' := is_st_add hx' hy' 
  is_st_unique hxy hxy'

theorem st_neg (x : ℝ*) : st (-x) = -st x :=
  if h : Infinite x then
    by 
      rw [st_infinite h, st_infinite (infinite_iff_infinite_neg.mp h), neg_zero]
  else is_st_unique (is_st_st' (not_infinite_neg h)) (is_st_neg (is_st_st' h))

theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x*y) = st x*st y :=
  have hx' := is_st_st' hx 
  have hy' := is_st_st' hy 
  have hxy := is_st_st' (not_infinite_mul hx hy)
  have hxy' := is_st_mul hx' hy' 
  is_st_unique hxy hxy'

/-!
### Basic lemmas about infinitesimal
-/


theorem infinitesimal_def {x : ℝ*} : infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r :=
  ⟨fun hi r hr =>
      by 
        convert hi r hr <;> simp ,
    fun hi d hd =>
      by 
        convert hi d hd <;> simp ⟩

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, 0 < r → -«expr↑ » r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ r : ℝ, r < 0 → «expr↑ » r < x :=
  fun hi r hr =>
    by 
      convert ((infinitesimal_def.mp hi) (-r) (neg_pos.mpr hr)).1 <;> exact (neg_negₓ («expr↑ » r)).symm

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |r| :=
  ⟨fun hi r hr =>
      abs_lt.mpr
        (by 
          rw [←coe_abs] <;> exact infinitesimal_def.mp hi |r| (abs_pos.2 hr)),
    fun hR => infinitesimal_def.mpr$ fun r hr => abs_lt.mp$ (abs_of_pos$ coe_pos.2 hr) ▸ hR r$ ne_of_gtₓ hr⟩

theorem infinitesimal_zero : infinitesimal 0 :=
  is_st_refl_real 0

theorem zero_of_infinitesimal_real {r : ℝ} : infinitesimal r → r = 0 :=
  eq_of_is_st_real

theorem zero_iff_infinitesimal_real {r : ℝ} : infinitesimal r ↔ r = 0 :=
  ⟨zero_of_infinitesimal_real,
    fun hr =>
      by 
        rw [hr] <;> exact infinitesimal_zero⟩

theorem infinitesimal_add {x y : ℝ*} (hx : infinitesimal x) (hy : infinitesimal y) : infinitesimal (x+y) :=
  by 
    simpa only [add_zeroₓ] using is_st_add hx hy

theorem infinitesimal_neg {x : ℝ*} (hx : infinitesimal x) : infinitesimal (-x) :=
  by 
    simpa only [neg_zero] using is_st_neg hx

theorem infinitesimal_neg_iff {x : ℝ*} : infinitesimal x ↔ infinitesimal (-x) :=
  ⟨infinitesimal_neg, fun h => neg_negₓ x ▸ @infinitesimal_neg (-x) h⟩

theorem infinitesimal_mul {x y : ℝ*} (hx : infinitesimal x) (hy : infinitesimal y) : infinitesimal (x*y) :=
  by 
    simpa only [mul_zero] using is_st_mul hx hy

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} : tendsto f at_top (𝓝 0) → infinitesimal (of_seq f) :=
  fun hf d hd =>
    by 
      rw [sub_eq_add_neg, ←coe_neg, ←coe_add, ←coe_add, zero_addₓ, zero_addₓ] <;>
        exact ⟨neg_lt_of_tendsto_zero_of_pos hf hd, lt_of_tendsto_zero_of_pos hf hd⟩

theorem infinitesimal_epsilon : infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inverse_at_top_nhds_0_nat

theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr => hx$ hr.trans$ coe_eq_zero.2$ is_st_unique (hr.symm ▸ is_st_refl_real r : is_st x r) hi

theorem infinitesimal_sub_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : infinitesimal (x - r) :=
  show is_st (x - r) 0 by 
    rw [sub_eq_add_neg, ←add_neg_selfₓ r]
    exact is_st_add hxr (is_st_refl_real (-r))

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : infinitesimal (x - st x) :=
  infinitesimal_sub_is_st$ is_st_st' hx

theorem infinite_pos_iff_infinitesimal_inv_pos {x : ℝ*} : infinite_pos x ↔ infinitesimal (x⁻¹) ∧ 0 < x⁻¹ :=
  ⟨fun hip =>
      ⟨infinitesimal_def.mpr$
          fun r hr =>
            ⟨lt_transₓ (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
              (inv_lt (coe_lt_coe.2 hr) (hip 0)).mp
                (by 
                  convert hip (r⁻¹))⟩,
        inv_pos.2$ hip 0⟩,
    fun ⟨hi, hp⟩ r =>
      (@Classical.by_cases (r = 0) («expr↑ » r < x) fun h => Eq.substr h (inv_pos.mp hp))$
        fun h =>
          lt_of_le_of_ltₓ (coe_le_coe.2 (le_abs_self r))
            ((inv_lt_inv (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
              ((infinitesimal_def.mp hi) (|r|⁻¹) (inv_pos.2 (abs_pos.2 h))).2)⟩

theorem infinite_neg_iff_infinitesimal_inv_neg {x : ℝ*} : infinite_neg x ↔ infinitesimal (x⁻¹) ∧ x⁻¹ < 0 :=
  ⟨fun hin =>
      have hin' := infinite_pos_iff_infinitesimal_inv_pos.mp (infinite_pos_neg_of_infinite_neg hin)
      by 
        rwa [infinitesimal_neg_iff, ←neg_pos, neg_inv],
    fun hin =>
      by 
        rwa [←neg_pos, infinitesimal_neg_iff, neg_inv, ←infinite_pos_iff_infinitesimal_inv_pos,
          ←infinite_neg_iff_infinite_pos_neg] at hin⟩

theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → infinitesimal (x⁻¹) :=
  fun hi =>
    Or.cases_on hi (fun hip => (infinite_pos_iff_infinitesimal_inv_pos.mp hip).1)
      fun hin => (infinite_neg_iff_infinitesimal_inv_neg.mp hin).1

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : infinitesimal (x⁻¹)) : Infinite x :=
  by 
    cases' lt_or_gt_of_neₓ h0 with hn hp
    ·
      exact Or.inr (infinite_neg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
    ·
      exact Or.inl (infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ infinitesimal (x⁻¹) :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

theorem infinitesimal_pos_iff_infinite_pos_inv {x : ℝ*} : infinite_pos (x⁻¹) ↔ infinitesimal x ∧ 0 < x :=
  by 
    convert infinite_pos_iff_infinitesimal_inv_pos <;> simp only [inv_inv₀]

theorem infinitesimal_neg_iff_infinite_neg_inv {x : ℝ*} : infinite_neg (x⁻¹) ↔ infinitesimal x ∧ x < 0 :=
  by 
    convert infinite_neg_iff_infinitesimal_inv_neg <;> simp only [inv_inv₀]

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : infinitesimal x ↔ Infinite (x⁻¹) :=
  by 
    convert (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm <;> simp only [inv_inv₀]

/-!
### `st` stuff that requires infinitesimal machinery
-/


theorem is_st_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : tendsto f at_top (𝓝 r)) : is_st (of_seq f) r :=
  have hg : tendsto (fun n => f n - r) at_top (𝓝 0) := sub_self r ▸ hf.sub tendsto_const_nhds 
  by 
    rw [←zero_addₓ r, ←sub_add_cancel f fun n => r] <;>
      exact is_st_add (infinitesimal_of_tendsto_zero hg) (is_st_refl_real r)

theorem is_st_inv {x : ℝ*} {r : ℝ} (hi : ¬infinitesimal x) : is_st x r → is_st (x⁻¹) (r⁻¹) :=
  fun hxr =>
    have h : x ≠ 0 := fun h => hi (h.symm ▸ infinitesimal_zero)
    have H := exists_st_of_not_infinite$ not_imp_not.mpr (infinitesimal_iff_infinite_inv h).mpr hi 
    Exists.cases_on H$
      fun s hs =>
        have H' : is_st 1 (r*s) := mul_inv_cancel h ▸ is_st_mul hxr hs 
        have H'' : s = r⁻¹ := one_div r ▸ eq_one_div_of_mul_eq_one (eq_of_is_st_real H').symm 
        H'' ▸ hs

theorem st_inv (x : ℝ*) : st (x⁻¹) = st x⁻¹ :=
  by 
    byCases' h0 : x = 0
    rw [h0, inv_zero, ←coe_zero, st_id_real, inv_zero]
    byCases' h1 : infinitesimal x 
    rw [st_infinite ((infinitesimal_iff_infinite_inv h0).mp h1), st_of_is_st h1, inv_zero]
    byCases' h2 : Infinite x 
    rw [st_of_is_st (infinitesimal_inv_of_infinite h2), st_infinite h2, inv_zero]
    exact st_of_is_st (is_st_inv h1 (is_st_st' h2))

/-!
### Infinite stuff that requires infinitesimal machinery
-/


theorem infinite_pos_omega : infinite_pos ω :=
  infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

theorem infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos {x y : ℝ*} :
  infinite_pos x → ¬infinitesimal y → 0 < y → infinite_pos (x*y) :=
  fun hx hy₁ hy₂ r =>
    have hy₁' :=
      not_forall.mp
        (by 
          rw [infinitesimal_def] at hy₁ <;> exact hy₁)
    Exists.dcases_on hy₁'$
      fun r₁ hy₁'' =>
        have hyr :=
          by 
            rw [not_imp, ←abs_lt, not_ltₓ, abs_of_pos hy₂] at hy₁'' <;> exact hy₁'' 
        by 
          rw [←div_mul_cancel r (ne_of_gtₓ hyr.1), coe_mul] <;>
            exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_ltₓ (hx 0))

theorem infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos {x y : ℝ*} :
  ¬infinitesimal x → 0 < x → infinite_pos y → infinite_pos (x*y) :=
  fun hx hp hy =>
    by 
      rw [mul_commₓ] <;> exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp

theorem infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg {x y : ℝ*} :
  infinite_neg x → ¬infinitesimal y → y < 0 → infinite_pos (x*y) :=
  by 
    rw [infinite_neg_iff_infinite_pos_neg, ←neg_pos, ←neg_mul_neg, infinitesimal_neg_iff] <;>
      exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

theorem infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg {x y : ℝ*} :
  ¬infinitesimal x → x < 0 → infinite_neg y → infinite_pos (x*y) :=
  fun hx hp hy =>
    by 
      rw [mul_commₓ] <;> exact infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp

theorem infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg {x y : ℝ*} :
  infinite_pos x → ¬infinitesimal y → y < 0 → infinite_neg (x*y) :=
  by 
    rw [infinite_neg_iff_infinite_pos_neg, ←neg_pos, neg_mul_eq_mul_neg, infinitesimal_neg_iff] <;>
      exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

theorem infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos {x y : ℝ*} :
  ¬infinitesimal x → x < 0 → infinite_pos y → infinite_neg (x*y) :=
  fun hx hp hy =>
    by 
      rw [mul_commₓ] <;> exact infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp

theorem infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos {x y : ℝ*} :
  infinite_neg x → ¬infinitesimal y → 0 < y → infinite_neg (x*y) :=
  by 
    rw [infinite_neg_iff_infinite_pos_neg, infinite_neg_iff_infinite_pos_neg, neg_mul_eq_neg_mul] <;>
      exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos

theorem infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg {x y : ℝ*} :
  ¬infinitesimal x → 0 < x → infinite_neg y → infinite_neg (x*y) :=
  fun hx hp hy =>
    by 
      rw [mul_commₓ] <;> exact infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp

theorem infinite_pos_mul_infinite_pos {x y : ℝ*} : infinite_pos x → infinite_pos y → infinite_pos (x*y) :=
  fun hx hy => infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

theorem infinite_neg_mul_infinite_neg {x y : ℝ*} : infinite_neg x → infinite_neg y → infinite_pos (x*y) :=
  fun hx hy => infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

theorem infinite_pos_mul_infinite_neg {x y : ℝ*} : infinite_pos x → infinite_neg y → infinite_neg (x*y) :=
  fun hx hy => infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy) (hy 0)

theorem infinite_neg_mul_infinite_pos {x y : ℝ*} : infinite_neg x → infinite_pos y → infinite_neg (x*y) :=
  fun hx hy => infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy) (hy 0)

theorem infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} : Infinite x → ¬infinitesimal y → Infinite (x*y) :=
  fun hx hy =>
    have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_neₓ fun H0 => hy (Eq.substr H0 (is_st_refl_real 0))
    Or.dcases_on hx
      (Or.dcases_on h0 (fun H0 Hx => Or.inr (infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hx hy H0))
        fun H0 Hx => Or.inl (infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hx hy H0))
      (Or.dcases_on h0 (fun H0 Hx => Or.inl (infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hx hy H0))
        fun H0 Hx => Or.inr (infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hx hy H0))

theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} : ¬infinitesimal x → Infinite y → Infinite (x*y) :=
  fun hx hy =>
    by 
      rw [mul_commₓ] <;> exact infinite_mul_of_infinite_not_infinitesimal hy hx

theorem infinite_mul_infinite {x y : ℝ*} : Infinite x → Infinite y → Infinite (x*y) :=
  fun hx hy => infinite_mul_of_infinite_not_infinitesimal hx (not_infinitesimal_of_infinite hy)

end Hyperreal

