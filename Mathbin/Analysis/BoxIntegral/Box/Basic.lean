import Mathbin.Topology.MetricSpace.Basic

/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `box_integral.box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `has_mem (ι → ℝ) (box ι)` and `has_coe_t (box ι) (set $ ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : with_bot (box_integral.box ι)`.

We define the following operations on boxes:

* coercion to `set (ι → ℝ)` and `has_mem (ι → ℝ) (box_integral.box ι)` as described above;
* `partial_order` and `semilattice_sup` instances such that `I ≤ J` is equivalent to
  `(I : set (ι → ℝ)) ⊆ J`;
* `lattice` instances on `with_bot (box_integral.box ι)`;
* `box_integral.box.Icc`: the closed box `set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `box ι` to `set (ι → ℝ)`;
* `box_integral.box.face I i : box (fin n)`: a hyperface of `I : box_integral.box (fin (n + 1))`;
* `box_integral.box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `box_integral.box.mk' (l u : ι → ℝ) : with_bot (box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

rectangular box
-/


open Set Function Metric

noncomputable theory

open_locale Nnreal Classical

namespace BoxIntegral

variable {ι : Type _}

/-!
### Rectangular box: definition and partial order
-/


/-- A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Repesents the product
of half-open intervals `(lower i, upper i]`. -/
structure box (ι : Type _) where 
  (lower upper : ι → ℝ)
  lower_lt_upper : ∀ i, lower i < upper i

attribute [simp] box.lower_lt_upper

namespace Box

variable (I J : box ι) {x y : ι → ℝ}

instance : Inhabited (box ι) :=
  ⟨⟨0, 1, fun i => zero_lt_one⟩⟩

theorem lower_le_upper : I.lower ≤ I.upper :=
  fun i => (I.lower_lt_upper i).le

instance : HasMem (ι → ℝ) (box ι) :=
  ⟨fun x I => ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)⟩

instance : CoeTₓ (box ι) (Set$ ι → ℝ) :=
  ⟨fun I => { x | x ∈ I }⟩

@[simp]
theorem mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) :=
  Iff.rfl

@[simp, normCast]
theorem mem_coe : x ∈ (I : Set (ι → ℝ)) ↔ x ∈ I :=
  Iff.rfl

theorem mem_def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) :=
  Iff.rfl

theorem mem_univ_Ioc {I : box ι} : (x ∈ pi univ fun i => Ioc (I.lower i) (I.upper i)) ↔ x ∈ I :=
  mem_univ_pi

theorem coe_eq_pi : (I : Set (ι → ℝ)) = pi univ fun i => Ioc (I.lower i) (I.upper i) :=
  Set.ext$ fun x => mem_univ_Ioc.symm

@[simp]
theorem upper_mem : I.upper ∈ I :=
  fun i => right_mem_Ioc.2$ I.lower_lt_upper i

theorem exists_mem : ∃ x, x ∈ I :=
  ⟨_, I.upper_mem⟩

theorem nonempty_coe : Set.Nonempty (I : Set (ι → ℝ)) :=
  I.exists_mem

@[simp]
theorem coe_ne_empty : (I : Set (ι → ℝ)) ≠ ∅ :=
  I.nonempty_coe.ne_empty

@[simp]
theorem empty_ne_coe : ∅ ≠ (I : Set (ι → ℝ)) :=
  I.coe_ne_empty.symm

instance : LE (box ι) :=
  ⟨fun I J => ∀ ⦃x⦄, x ∈ I → x ∈ J⟩

theorem le_def : I ≤ J ↔ ∀ x _ : x ∈ I, x ∈ J :=
  Iff.rfl

theorem le_tfae :
  tfae
    [I ≤ J, (I : Set (ι → ℝ)) ⊆ J, Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lower ≤ I.lower ∧ I.upper ≤ J.upper] :=
  by 
    tfaeHave 1 ↔ 2 
    exact Iff.rfl 
    tfaeHave 2 → 3 
    exact
      fun h =>
        by 
          simpa [coe_eq_pi, closure_pi_set] using closure_mono h 
    tfaeHave 3 ↔ 4 
    exact Icc_subset_Icc_iff I.lower_le_upper 
    tfaeHave 4 → 2 
    exact fun h x hx i => Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
    tfaeFinish

variable {I J}

@[simp, normCast]
theorem coe_subset_coe : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J :=
  Iff.rfl

theorem le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper :=
  (le_tfae I J).out 0 3

theorem injective_coe : injective (coeₓ : box ι → Set (ι → ℝ)) :=
  by 
    rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h 
    simp only [subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h 
    congr 
    exacts[le_antisymmₓ h.2.1 h.1.1, le_antisymmₓ h.1.2 h.2.2]

@[simp, normCast]
theorem coe_inj : (I : Set (ι → ℝ)) = J ↔ I = J :=
  injective_coe.eq_iff

@[ext]
theorem ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  injective_coe$ Set.ext H

theorem ne_of_disjoint_coe (h : Disjoint (I : Set (ι → ℝ)) J) : I ≠ J :=
  mt coe_inj.2$ h.ne I.coe_ne_empty

instance : PartialOrderₓ (box ι) :=
  { PartialOrderₓ.lift (coeₓ : box ι → Set (ι → ℝ)) injective_coe with le := · ≤ · }

/-- Closed box corresponding to `I : box_integral.box ι`. -/
protected def Icc : box ι ↪o Set (ι → ℝ) :=
  OrderEmbedding.ofMapLeIff (fun I : box ι => Icc I.lower I.upper) fun I J => (le_tfae I J).out 2 0

theorem Icc_def : I.Icc = Icc I.lower I.upper :=
  rfl

@[simp]
theorem upper_mem_Icc (I : box ι) : I.upper ∈ I.Icc :=
  right_mem_Icc.2 I.lower_le_upper

@[simp]
theorem lower_mem_Icc (I : box ι) : I.lower ∈ I.Icc :=
  left_mem_Icc.2 I.lower_le_upper

protected theorem is_compact_Icc (I : box ι) : IsCompact I.Icc :=
  is_compact_Icc

theorem Icc_eq_pi : I.Icc = pi univ fun i => Icc (I.lower i) (I.upper i) :=
  (pi_univ_Icc _ _).symm

theorem le_iff_Icc : I ≤ J ↔ I.Icc ⊆ J.Icc :=
  (le_tfae I J).out 0 2

theorem antitone_lower : Antitone fun I : box ι => I.lower :=
  fun I J H => (le_iff_bounds.1 H).1

theorem monotone_upper : Monotone fun I : box ι => I.upper :=
  fun I J H => (le_iff_bounds.1 H).2

theorem coe_subset_Icc : «expr↑ » I ⊆ I.Icc :=
  fun x hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

/-!
### Supremum of two boxes
-/


/-- `I ⊔ J` is the least box that includes both `I` and `J`. Since `↑I ∪ ↑J` is usually not a box,
`↑(I ⊔ J)` is larger than `↑I ∪ ↑J`. -/
instance : HasSup (box ι) :=
  ⟨fun I J =>
      ⟨I.lower⊓J.lower, I.upper⊔J.upper,
        fun i => (min_le_leftₓ _ _).trans_lt$ (I.lower_lt_upper i).trans_le (le_max_leftₓ _ _)⟩⟩

instance : SemilatticeSup (box ι) :=
  { box.partial_order, box.has_sup with le_sup_left := fun I J => le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩,
    le_sup_right := fun I J => le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩,
    sup_le :=
      fun I₁ I₂ J h₁ h₂ =>
        le_iff_bounds.2
          ⟨le_inf (antitone_lower h₁) (antitone_lower h₂), sup_le (monotone_upper h₁) (monotone_upper h₂)⟩ }

/-!
### `with_bot (box ι)`

In this section we define coercion from `with_bot (box ι)` to `set (ι → ℝ)` by sending `⊥` to `∅`.
-/


instance with_bot_coe : CoeTₓ (WithBot (box ι)) (Set (ι → ℝ)) :=
  ⟨fun o => o.elim ∅ coeₓ⟩

@[simp, normCast]
theorem coe_bot : ((⊥ : WithBot (box ι)) : Set (ι → ℝ)) = ∅ :=
  rfl

@[simp, normCast]
theorem coe_coe : ((I : WithBot (box ι)) : Set (ι → ℝ)) = I :=
  rfl

theorem is_some_iff : ∀ {I : WithBot (box ι)}, I.is_some ↔ (I : Set (ι → ℝ)).Nonempty
| ⊥ =>
  by 
    erw [Option.isSome]
    simp 
| (I : box ι) =>
  by 
    erw [Option.isSome]
    simp [I.nonempty_coe]

theorem bUnion_coe_eq_coe (I : WithBot (box ι)) : (⋃(J : box ι)(hJ : «expr↑ » J = I), (J : Set (ι → ℝ))) = I :=
  by 
    induction I using WithBot.recBotCoe <;> simp [WithBot.coe_eq_coe]

@[simp, normCast]
theorem with_bot_coe_subset_iff {I J : WithBot (box ι)} : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J :=
  by 
    induction I using WithBot.recBotCoe
    ·
      simp 
    induction J using WithBot.recBotCoe
    ·
      simp [subset_empty_iff]
    simp 

@[simp, normCast]
theorem with_bot_coe_inj {I J : WithBot (box ι)} : (I : Set (ι → ℝ)) = J ↔ I = J :=
  by 
    simp only [subset.antisymm_iff, ←le_antisymm_iffₓ, with_bot_coe_subset_iff]

/-- Make a `with_bot (box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` for all `i`,
then the result is `⟨l, u, _⟩ : box ι`, otherwise it is `⊥`. In any case, the result interpreted
as a set in `ι → ℝ` is the set `{x : ι → ℝ | ∀ i, x i ∈ Ioc (l i) (u i)}`.  -/
def mk' (l u : ι → ℝ) : WithBot (box ι) :=
  if h : ∀ i, l i < u i then «expr↑ » (⟨l, u, h⟩ : box ι) else ⊥

@[simp]
theorem mk'_eq_bot {l u : ι → ℝ} : mk' l u = ⊥ ↔ ∃ i, u i ≤ l i :=
  by 
    rw [mk']
    splitIfs <;> simpa using h

@[simp]
theorem mk'_eq_coe {l u : ι → ℝ} : mk' l u = I ↔ l = I.lower ∧ u = I.upper :=
  by 
    cases' I with lI uI hI 
    rw [mk']
    splitIfs
    ·
      simp [WithBot.coe_eq_coe]
    ·
      suffices  : l = lI → u ≠ uI
      ·
        simpa 
      rintro rfl rfl 
      exact h hI

@[simp]
theorem coe_mk' (l u : ι → ℝ) : (mk' l u : Set (ι → ℝ)) = pi univ fun i => Ioc (l i) (u i) :=
  by 
    rw [mk']
    splitIfs
    ·
      exact coe_eq_pi _
    ·
      rcases not_forall.mp h with ⟨i, hi⟩
      rw [coe_bot, univ_pi_eq_empty]
      exact Ioc_eq_empty hi

instance : HasInf (WithBot (box ι)) :=
  ⟨fun I =>
      WithBot.recBotCoe (fun J => ⊥)
        (fun I J => WithBot.recBotCoe ⊥ (fun J => mk' (I.lower⊔J.lower) (I.upper⊓J.upper)) J) I⟩

@[simp]
theorem coe_inf (I J : WithBot (box ι)) : («expr↑ » (I⊓J) : Set (ι → ℝ)) = I ∩ J :=
  by 
    induction I using WithBot.recBotCoe
    ·
      change ∅ = _ 
      simp 
    induction J using WithBot.recBotCoe
    ·
      change ∅ = _ 
      simp 
    change «expr↑ » (mk' _ _) = _ 
    simp only [coe_eq_pi, ←pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk', coe_coe]

instance : Lattice (WithBot (box ι)) :=
  { WithBot.semilatticeSup, box.with_bot.has_inf with
    inf_le_left :=
      fun I J =>
        by 
          rw [←with_bot_coe_subset_iff, coe_inf]
          exact inter_subset_left _ _,
    inf_le_right :=
      fun I J =>
        by 
          rw [←with_bot_coe_subset_iff, coe_inf]
          exact inter_subset_right _ _,
    le_inf :=
      fun I J₁ J₂ h₁ h₂ =>
        by 
          simp only [←with_bot_coe_subset_iff, coe_inf] at *
          exact subset_inter h₁ h₂ }

@[simp, normCast]
theorem disjoint_with_bot_coe {I J : WithBot (box ι)} : Disjoint (I : Set (ι → ℝ)) J ↔ Disjoint I J :=
  by 
    simp only [Disjoint, ←with_bot_coe_subset_iff, coe_inf]
    rfl

theorem disjoint_coe : Disjoint (I : WithBot (box ι)) J ↔ Disjoint (I : Set (ι → ℝ)) J :=
  disjoint_with_bot_coe.symm

theorem not_disjoint_coe_iff_nonempty_inter : ¬Disjoint (I : WithBot (box ι)) J ↔ (I ∩ J : Set (ι → ℝ)).Nonempty :=
  by 
    rw [disjoint_coe, Set.not_disjoint_iff_nonempty_inter]

/-!
### Hyperface of a box in `ℝⁿ⁺¹ = fin (n + 1) → ℝ`
-/


/-- Face of a box in `ℝⁿ⁺¹ = fin (n + 1) → ℝ`: the box in `ℝⁿ = fin n → ℝ` with corners at
`I.lower ∘ fin.succ_above i` and `I.upper ∘ fin.succ_above i`. -/
@[simps]
def face {n} (I : box (Finₓ (n+1))) (i : Finₓ (n+1)) : box (Finₓ n) :=
  ⟨I.lower ∘ Finₓ.succAbove i, I.upper ∘ Finₓ.succAbove i, fun j => I.lower_lt_upper _⟩

@[simp]
theorem face_mk {n} (l u : Finₓ (n+1) → ℝ) (h : ∀ i, l i < u i) (i : Finₓ (n+1)) :
  face ⟨l, u, h⟩ i = ⟨l ∘ Finₓ.succAbove i, u ∘ Finₓ.succAbove i, fun j => h _⟩ :=
  rfl

@[mono]
theorem face_mono {n} {I J : box (Finₓ (n+1))} (h : I ≤ J) (i : Finₓ (n+1)) : face I i ≤ face J i :=
  fun x hx i => Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)

theorem maps_to_insert_nth_face_Icc {n} (I : box (Finₓ (n+1))) {i : Finₓ (n+1)} {x : ℝ}
  (hx : x ∈ Icc (I.lower i) (I.upper i)) : maps_to (i.insert_nth x) (I.face i).Icc I.Icc :=
  fun y hy => Finₓ.insert_nth_mem_Icc.2 ⟨hx, hy⟩

theorem maps_to_insert_nth_face {n} (I : box (Finₓ (n+1))) {i : Finₓ (n+1)} {x : ℝ}
  (hx : x ∈ Ioc (I.lower i) (I.upper i)) : maps_to (i.insert_nth x) (I.face i) I :=
  fun y hy =>
    by 
      simpa only [mem_coe, mem_def, i.forall_iff_succ_above, hx, Finₓ.insert_nth_apply_same,
        Finₓ.insert_nth_apply_succ_above, true_andₓ]

theorem continuous_on_face_Icc {X} [TopologicalSpace X] {n} {f : (Finₓ (n+1) → ℝ) → X} {I : box (Finₓ (n+1))}
  (h : ContinuousOn f I.Icc) {i : Finₓ (n+1)} {x : ℝ} (hx : x ∈ Icc (I.lower i) (I.upper i)) :
  ContinuousOn (f ∘ i.insert_nth x) (I.face i).Icc :=
  h.comp (continuous_on_const.fin_insert_nth i continuous_on_id) (I.maps_to_insert_nth_face_Icc hx)

section Distortion

variable [Fintype ι]

/-- The distortion of a box `I` is the maximum of the ratios of the lengths of its edges.
It is defined as the maximum of the ratios
`nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`. -/
def distortion (I : box ι) :  ℝ≥0  :=
  Finset.univ.sup$ fun i : ι => nndist I.lower I.upper / nndist (I.lower i) (I.upper i)

-- error in Analysis.BoxIntegral.Box.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem distortion_eq_of_sub_eq_div
{I J : box ι}
{r : exprℝ()}
(h : ∀
 i, «expr = »(«expr - »(I.upper i, I.lower i), «expr / »(«expr - »(J.upper i, J.lower i), r))) : «expr = »(distortion I, distortion J) :=
begin
  simp [] [] ["only"] ["[", expr distortion, ",", expr nndist_pi_def, ",", expr real.nndist_eq', ",", expr h, ",", expr real.nnabs.map_div, "]"] [] [],
  congr' [1] ["with", ident i],
  have [] [":", expr «expr < »(0, r)] [],
  { by_contra [ident hr],
    have [] [] [":=", expr div_nonpos_of_nonneg_of_nonpos «expr $ »(sub_nonneg.2, J.lower_le_upper i) (not_lt.1 hr)],
    rw ["<-", expr h] ["at", ident this],
    exact [expr this.not_lt «expr $ »(sub_pos.2, I.lower_lt_upper i)] },
  simp [] [] ["only"] ["[", expr nnreal.finset_sup_div, ",", expr div_div_div_cancel_right _ (real.nnabs.map_ne_zero.2 this.ne'), "]"] [] []
end

theorem nndist_le_distortion_mul (I : box ι) (i : ι) :
  nndist I.lower I.upper ≤ I.distortion*nndist (I.lower i) (I.upper i) :=
  calc
    nndist I.lower I.upper = (nndist I.lower I.upper / nndist (I.lower i) (I.upper i))*nndist (I.lower i) (I.upper i) :=
    (div_mul_cancel _$ mt nndist_eq_zero.1 (I.lower_lt_upper i).Ne).symm 
    _ ≤ I.distortion*nndist (I.lower i) (I.upper i) := mul_le_mul_right' (Finset.le_sup$ Finset.mem_univ i) _
    

theorem dist_le_distortion_mul (I : box ι) (i : ι) : dist I.lower I.upper ≤ I.distortion*I.upper i - I.lower i :=
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  by 
    simpa only [←Nnreal.coe_le_coe, ←dist_nndist, Nnreal.coe_mul, Real.dist_eq, abs_of_neg A, neg_sub] using
      I.nndist_le_distortion_mul i

theorem diam_Icc_le_of_distortion_le (I : box ι) (i : ι) {c :  ℝ≥0 } (h : I.distortion ≤ c) :
  diam I.Icc ≤ c*I.upper i - I.lower i :=
  have  : (0 : ℝ) ≤ c*I.upper i - I.lower i := mul_nonneg c.coe_nonneg (sub_nonneg.2$ I.lower_le_upper _)
  diam_le_of_forall_dist_le this$
    fun x hx y hy =>
      calc dist x y ≤ dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy 
        _ ≤ I.distortion*I.upper i - I.lower i := I.dist_le_distortion_mul i 
        _ ≤ c*I.upper i - I.lower i := mul_le_mul_of_nonneg_right h (sub_nonneg.2 (I.lower_le_upper i))
        

end Distortion

end Box

end BoxIntegral

