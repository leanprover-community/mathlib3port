import Mathbin.Analysis.BoxIntegral.Partition.Split 
import Mathbin.Analysis.NormedSpace.OperatorNorm 
import Mathbin.Data.Set.Intervals.ProjIcc

/-!
# Box additive functions

We say that a function `f : box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : with_top (box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' in π.boxes, f J'`. We use `I₀ : with_top (box ι)` instead of `I₀ : box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

### Tags

rectangular box, additive function
-/


noncomputable theory

open_locale Classical BigOperators

open Function Set

namespace BoxIntegral

variable {ι M : Type _} {n : ℕ}

/-- A function on `box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji in π.boxes, f Ji`. A function is called box additive on subboxes of `I : box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the same definition
using `I : with_bot (box ι)`: the value `I = ⊤` corresponds to functions box additive on the whole
space.  -/
structure box_additive_map (ι M : Type _) [AddCommMonoidₓ M] (I : WithTop (box ι)) where 
  toFun : box ι → M 
  sum_partition_boxes' :
  ∀ J : box ι, «expr↑ » J ≤ I → ∀ π : prepartition J, π.is_partition → (∑Ji in π.boxes, to_fun Ji) = to_fun J

localized [BoxIntegral] notation:25 ι " →ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤

localized [BoxIntegral] notation:25 ι " →ᵇᵃ[" I "] " M => BoxIntegral.BoxAdditiveMap ι M I

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type _} [AddCommMonoidₓ M] [AddCommMonoidₓ N] {I₀ : WithTop (box ι)} {I J : box ι} {i : ι}

instance : CoeFun (ι →ᵇᵃ[I₀] M) fun _ => box ι → M :=
  ⟨to_fun⟩

initialize_simps_projections box_integral.box_additive_map (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : ι →ᵇᵃ[I₀] M) : f.to_fun = f :=
  rfl

@[simp]
theorem coe_mk f h : «expr⇑ » (mk f h : ι →ᵇᵃ[I₀] M) = f :=
  rfl

theorem coe_injective : injective fun f : ι →ᵇᵃ[I₀] M x => f x :=
  by 
    rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g)
    rfl

@[simp]
theorem coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : box ι → M) = g ↔ f = g :=
  coe_injective.eq_iff

theorem sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : «expr↑ » I ≤ I₀) {π : prepartition I} (h : π.is_partition) :
  (∑J in π.boxes, f J) = f I :=
  f.sum_partition_boxes' I hI π h

@[simps (config := { fullyApplied := ff })]
instance : HasZero (ι →ᵇᵃ[I₀] M) :=
  ⟨⟨0, fun I hI π hπ => sum_const_zero⟩⟩

instance : Inhabited (ι →ᵇᵃ[I₀] M) :=
  ⟨0⟩

instance : Add (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
      ⟨f+g,
        fun I hI π hπ =>
          by 
            simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance : AddCommMonoidₓ (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommMonoid _ coe_injective rfl fun _ _ => rfl

@[simp]
theorem map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : «expr↑ » I ≤ I₀) (i : ι) (x : ℝ) :
  ((I.split_lower i x).elim 0 f+(I.split_upper i x).elim 0 f) = f I :=
  by 
    rw [←f.sum_partition_boxes hI (is_partition_split I i x), sum_split_boxes]

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps]
def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩

-- error in Analysis.BoxIntegral.Partition.Additive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
def of_map_split_add
[fintype ι]
(f : box ι → M)
(I₀ : with_top (box ι))
(hf : ∀
 I : box ι, «expr ≤ »(«expr↑ »(I), I₀) → ∀
 {i
  x}, «expr ∈ »(x, Ioo (I.lower i) (I.upper i)) → «expr = »(«expr + »((I.split_lower i x).elim 0 f, (I.split_upper i x).elim 0 f), f I)) : «expr →ᵇᵃ[ ] »(ι, I₀, M) :=
begin
  refine [expr ⟨f, _⟩],
  replace [ident hf] [":", expr ∀
   I : box ι, «expr ≤ »(«expr↑ »(I), I₀) → ∀ s, «expr = »(«expr∑ in , »((J), (split_many I s).boxes, f J), f I)] [],
  { intros [ident I, ident hI, ident s],
    induction [expr s] ["using", ident finset.induction_on] ["with", ident a, ident s, ident ha, ident ihs] [],
    { simp [] [] [] [] [] [] },
    rw ["[", expr split_many_insert, ",", expr inf_split, ",", "<-", expr ihs, ",", expr bUnion_boxes, ",", expr sum_bUnion_boxes, "]"] [],
    refine [expr finset.sum_congr rfl (λ J' hJ', _)],
    by_cases [expr h, ":", expr «expr ∈ »(a.2, Ioo (J'.lower a.1) (J'.upper a.1))],
    { rw [expr sum_split_boxes] [],
      exact [expr hf _ («expr $ »(with_top.coe_le_coe.2, le_of_mem _ hJ').trans hI) h] },
    { rw ["[", expr split_of_not_mem_Ioo h, ",", expr top_boxes, ",", expr finset.sum_singleton, "]"] [] } },
  intros [ident I, ident hI, ident π, ident hπ],
  have [ident Hle] [":", expr ∀ J «expr ∈ » π, «expr ≤ »(«expr↑ »(J), I₀)] [],
  from [expr λ J hJ, «expr $ »(with_top.coe_le_coe.2, π.le_of_mem hJ).trans hI],
  rcases [expr hπ.exists_split_many_le, "with", "⟨", ident s, ",", ident hs, "⟩"],
  rw ["[", "<-", expr hf _ hI, ",", "<-", expr inf_of_le_right hs, ",", expr inf_split_many, ",", expr bUnion_boxes, ",", expr sum_bUnion_boxes, "]"] [],
  exact [expr finset.sum_congr rfl (λ J hJ, (hf _ (Hle _ hJ) _).symm)]
end

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps (config := { fullyApplied := ff })]
def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) : ι →ᵇᵃ[I₀] N :=
  { toFun := g ∘ f,
    sum_partition_boxes' :=
      fun I hI π hπ =>
        by 
          rw [←g.map_sum, f.sum_partition_boxes hI hπ] }

/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J`. -/
theorem sum_boxes_congr [Fintype ι] (f : ι →ᵇᵃ[I₀] M) (hI : «expr↑ » I ≤ I₀) {π₁ π₂ : prepartition I}
  (h : π₁.Union = π₂.Union) : (∑J in π₁.boxes, f J) = ∑J in π₂.boxes, f J :=
  by 
    rcases exists_split_many_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with ⟨s, hs⟩
    simp only [inf_split_many] at hs 
    rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩
    clear hs 
    rw [h] at h₁ 
    calc (∑J in π₁.boxes, f J) = ∑J in π₁.boxes, ∑J' in (split_many J s).boxes, f J' :=
      Finset.sum_congr rfl
        fun J hJ =>
          (f.sum_partition_boxes _ (is_partition_split_many _ _)).symm
            _ = ∑J in (π₁.bUnion fun J => split_many J s).boxes, f J :=
      (sum_bUnion_boxes _ _ _).symm _ = ∑J in (π₂.bUnion fun J => split_many J s).boxes, f J :=
      by 
        rw [h₁, h₂]_ = ∑J in π₂.boxes, ∑J' in (split_many J s).boxes, f J' :=
      sum_bUnion_boxes _ _ _ _ = ∑J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes _ (is_partition_split_many _ _)
    exacts[(WithTop.coe_le_coe.2$ π₁.le_of_mem hJ).trans hI, (WithTop.coe_le_coe.2$ π₂.le_of_mem hJ).trans hI]

section ToSmul

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E]

/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
def to_smul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] E →L[ℝ] E :=
  f.map (ContinuousLinearMap.lsmul ℝ ℝ).toLinearMap.toAddMonoidHom

@[simp]
theorem to_smul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : box ι) (x : E) : f.to_smul I x = f I • x :=
  rfl

end ToSmul

-- error in Analysis.BoxIntegral.Partition.Additive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : box (fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `λ J, f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes of
`I₀`. -/
@[simps #[]]
def upper_sub_lower.{u}
{G : Type u}
[add_comm_group G]
(I₀ : box (fin «expr + »(n, 1)))
(i : fin «expr + »(n, 1))
(f : exprℝ() → box (fin n) → G)
(fb : Icc (I₀.lower i) (I₀.upper i) → «expr →ᵇᵃ[ ] »(fin n, I₀.face i, G))
(hf : ∀
 (x)
 (hx : «expr ∈ »(x, Icc (I₀.lower i) (I₀.upper i)))
 (J), «expr = »(f x J, fb ⟨x, hx⟩ J)) : «expr →ᵇᵃ[ ] »(fin «expr + »(n, 1), I₀, G) :=
of_map_split_add (λ
 J : box (fin «expr + »(n, 1)), «expr - »(f (J.upper i) (J.face i), f (J.lower i) (J.face i))) I₀ (begin
   intros [ident J, ident hJ, ident j],
   rw [expr with_top.coe_le_coe] ["at", ident hJ],
   refine [expr i.succ_above_cases _ _ j],
   { intros [ident x, ident hx],
     simp [] [] ["only"] ["[", expr box.split_lower_def hx, ",", expr box.split_upper_def hx, ",", expr update_same, ",", "<-", expr with_bot.some_eq_coe, ",", expr option.elim, ",", expr box.face, ",", expr («expr ∘ »), ",", expr update_noteq (fin.succ_above_ne _ _), "]"] [] [],
     abel [] [] [] },
   { clear [ident j],
     intros [ident j, ident x, ident hx],
     have [] [":", expr «expr ≤ »((J.face i : with_top (box (fin n))), I₀.face i)] [],
     from [expr with_top.coe_le_coe.2 (face_mono hJ i)],
     rw ["[", expr le_iff_Icc, ",", expr @box.Icc_eq_pi _ I₀, "]"] ["at", ident hJ],
     rw ["[", expr hf _ (hJ J.upper_mem_Icc _ trivial), ",", expr hf _ (hJ J.lower_mem_Icc _ trivial), ",", "<-", expr (fb _).map_split_add this j x, ",", "<-", expr (fb _).map_split_add this j x, "]"] [],
     have [ident hx'] [":", expr «expr ∈ »(x, Ioo ((J.face i).lower j) ((J.face i).upper j))] [":=", expr hx],
     simp [] [] ["only"] ["[", expr box.split_lower_def hx, ",", expr box.split_upper_def hx, ",", expr box.split_lower_def hx', ",", expr box.split_upper_def hx', ",", "<-", expr with_bot.some_eq_coe, ",", expr option.elim, ",", expr box.face_mk, ",", expr update_noteq (fin.succ_above_ne _ _).symm, ",", expr sub_add_comm, ",", expr update_comp_eq_of_injective _ i.succ_above.injective j x, ",", "<-", expr hf, "]"] [] [],
     simp [] [] ["only"] ["[", expr box.face, "]"] [] [] }
 end)

end BoxAdditiveMap

end BoxIntegral

