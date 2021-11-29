import Mathbin.GroupTheory.Perm.Support 
import Mathbin.Data.Fintype.Basic 
import Mathbin.GroupTheory.OrderOfElement 
import Mathbin.Tactic.NormSwap 
import Mathbin.Data.Finset.Sort

/-!
# Sign of a permutation

The main definition of this file is `equiv.perm.sign`, associating a `units ℤ` sign with a
permutation.

This file also contains miscellaneous lemmas about `equiv.perm` and `equiv.swap`, building on top
of those in `data/equiv/basic` and other files in `group_theory/perm/*`.

-/


universe u v

open Equiv Function Fintype Finset

open_locale BigOperators

variable {α : Type u} {β : Type v}

namespace Equiv.Perm

/--
`mod_swap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `matrix.det_zero_of_row_eq`, such that each partition
sums up to `0`.
-/
def mod_swap [DecidableEq α] (i j : α) : Setoidₓ (perm α) :=
  ⟨fun σ τ => σ = τ ∨ σ = swap i j*τ, fun σ => Or.inl (refl σ),
    fun σ τ h =>
      Or.cases_on h (fun h => Or.inl h.symm)
        fun h =>
          Or.inr
            (by 
              rw [h, swap_mul_self_mul]),
    fun σ τ υ hστ hτυ =>
      by 
        cases hστ <;>
          cases hτυ <;>
            try 
                rw [hστ, hτυ, swap_mul_self_mul] <;>
              finish⟩

instance {α : Type _} [Fintype α] [DecidableEq α] (i j : α) : DecidableRel (mod_swap i j).R :=
  fun σ τ => Or.decidable

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm_inv_on_of_perm_on_finset
{s : finset α}
{f : perm α}
(h : ∀ x «expr ∈ » s, «expr ∈ »(f x, s))
{y : α}
(hy : «expr ∈ »(y, s)) : «expr ∈ »(«expr ⁻¹»(f) y, s) :=
begin
  have [ident h0] [":", expr ∀
   y «expr ∈ » s, «expr∃ , »((x)
    (hx : «expr ∈ »(x, s)), «expr = »(y, λ
     (i)
     (hi : «expr ∈ »(i, s)), f i x hx))] [":=", expr finset.surj_on_of_inj_on_of_card_le (λ
    x hx, λ i hi, f i x hx) (λ a ha, h a ha) (λ a₁ a₂ ha₁ ha₂ heq, (equiv.apply_eq_iff_eq f).mp heq) rfl.ge],
  obtain ["⟨", ident y2, ",", ident hy2, ",", ident heq, "⟩", ":=", expr h0 y hy],
  convert [] [expr hy2] [],
  rw [expr heq] [],
  simp [] [] ["only"] ["[", expr inv_apply_self, "]"] [] []
end

theorem perm_inv_maps_to_of_maps_to (f : perm α) {s : Set α} [Fintype s] (h : Set.MapsTo f s s) :
  Set.MapsTo (f⁻¹ : _) s s :=
  fun x hx =>
    Set.mem_to_finset.mp$
      perm_inv_on_of_perm_on_finset (fun a ha => Set.mem_to_finset.mpr (h (Set.mem_to_finset.mp ha)))
        (Set.mem_to_finset.mpr hx)

@[simp]
theorem perm_inv_maps_to_iff_maps_to {f : perm α} {s : Set α} [Fintype s] :
  Set.MapsTo (f⁻¹ : _) s s ↔ Set.MapsTo f s s :=
  ⟨perm_inv_maps_to_of_maps_to (f⁻¹), perm_inv_maps_to_of_maps_to f⟩

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm_inv_on_of_perm_on_fintype
{f : perm α}
{p : α → exprProp()}
[fintype {x // p x}]
(h : ∀ x, p x → p (f x))
{x : α}
(hx : p x) : p («expr ⁻¹»(f) x) :=
begin
  letI [] [":", expr fintype «expr↥ »(show set α, from p)] [":=", expr «expr‹ ›»(fintype {x // p x})],
  exact [expr perm_inv_maps_to_of_maps_to f h hx]
end

/-- If the permutation `f` maps `{x // p x}` into itself, then this returns the permutation
  on `{x // p x}` induced by `f`. Note that the `h` hypothesis is weaker than for
  `equiv.perm.subtype_perm`. -/
abbrev subtype_perm_of_fintype (f : perm α) {p : α → Prop} [Fintype { x // p x }] (h : ∀ x, p x → p (f x)) :
  perm { x // p x } :=
  f.subtype_perm fun x => ⟨h x, fun h₂ => f.inv_apply_self x ▸ perm_inv_on_of_perm_on_fintype h h₂⟩

@[simp]
theorem subtype_perm_of_fintype_apply (f : perm α) {p : α → Prop} [Fintype { x // p x }] (h : ∀ x, p x → p (f x))
  (x : { x // p x }) : subtype_perm_of_fintype f h x = ⟨f x, h x x.2⟩ :=
  rfl

@[simp]
theorem subtype_perm_of_fintype_one (p : α → Prop) [Fintype { x // p x }] (h : ∀ x, p x → p ((1 : perm α) x)) :
  @subtype_perm_of_fintype α 1 p _ h = 1 :=
  Equiv.ext$ fun ⟨_, _⟩ => rfl

theorem perm_maps_to_inl_iff_maps_to_inr {m n : Type _} [Fintype m] [Fintype n] (σ : Equiv.Perm (Sum m n)) :
  Set.MapsTo σ (Set.Range Sum.inl) (Set.Range Sum.inl) ↔ Set.MapsTo σ (Set.Range Sum.inr) (Set.Range Sum.inr) :=
  by 
    split  <;>
      (
        intro h 
        classical 
        rw [←perm_inv_maps_to_iff_maps_to] at h 
        intro x 
        cases' hx : σ x with l r)
    ·
      rintro ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
      rw [←hx, σ.inv_apply_self] at hy 
      exact absurd hy Sum.inl_ne_inr
    ·
      rintro ⟨a, ha⟩
      exact ⟨r, rfl⟩
    ·
      rintro ⟨a, ha⟩
      exact ⟨l, rfl⟩
    ·
      rintro ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
      rw [←hx, σ.inv_apply_self] at hy 
      exact absurd hy Sum.inr_ne_inl

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_sum_congr_hom_range_of_perm_maps_to_inl
{m n : Type*}
[fintype m]
[fintype n]
{σ : perm «expr ⊕ »(m, n)}
(h : set.maps_to σ (set.range sum.inl) (set.range sum.inl)) : «expr ∈ »(σ, (sum_congr_hom m n).range) :=
begin
  classical,
  have [ident h1] [":", expr ∀
   x : «expr ⊕ »(m, n), «expr∃ , »((a : m), «expr = »(sum.inl a, x)) → «expr∃ , »((a : m), «expr = »(sum.inl a, σ x))] [],
  { rintros [ident x, "⟨", ident a, ",", ident ha, "⟩"],
    apply [expr h],
    rw ["<-", expr ha] [],
    exact [expr ⟨a, rfl⟩] },
  have [ident h3] [":", expr ∀
   x : «expr ⊕ »(m, n), «expr∃ , »((b : n), «expr = »(sum.inr b, x)) → «expr∃ , »((b : n), «expr = »(sum.inr b, σ x))] [],
  { rintros [ident x, "⟨", ident b, ",", ident hb, "⟩"],
    apply [expr (perm_maps_to_inl_iff_maps_to_inr σ).mp h],
    rw ["<-", expr hb] [],
    exact [expr ⟨b, rfl⟩] },
  let [ident σ₁'] [] [":=", expr subtype_perm_of_fintype σ h1],
  let [ident σ₂'] [] [":=", expr subtype_perm_of_fintype σ h3],
  let [ident σ₁] [] [":=", expr perm_congr (equiv.of_injective (@sum.inl m n) sum.inl_injective).symm σ₁'],
  let [ident σ₂] [] [":=", expr perm_congr (equiv.of_injective (@sum.inr m n) sum.inr_injective).symm σ₂'],
  rw ["[", expr monoid_hom.mem_range, ",", expr prod.exists, "]"] [],
  use ["[", expr σ₁, ",", expr σ₂, "]"],
  rw ["[", expr perm.sum_congr_hom_apply, "]"] [],
  ext [] [] [],
  cases [expr x] ["with", ident a, ident b],
  { rw ["[", expr equiv.sum_congr_apply, ",", expr sum.map_inl, ",", expr perm_congr_apply, ",", expr equiv.symm_symm, ",", expr apply_of_injective_symm (@sum.inl m n), "]"] [],
    erw [expr subtype_perm_apply] [],
    rw ["[", expr of_injective_apply, ",", expr subtype.coe_mk, ",", expr subtype.coe_mk, "]"] [] },
  { rw ["[", expr equiv.sum_congr_apply, ",", expr sum.map_inr, ",", expr perm_congr_apply, ",", expr equiv.symm_symm, ",", expr apply_of_injective_symm (@sum.inr m n), "]"] [],
    erw [expr subtype_perm_apply] [],
    rw ["[", expr of_injective_apply, ",", expr subtype.coe_mk, ",", expr subtype.coe_mk, "]"] [] }
end

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem disjoint.order_of
{σ τ : perm α}
(hστ : disjoint σ τ) : «expr = »(order_of «expr * »(σ, τ), nat.lcm (order_of σ) (order_of τ)) :=
begin
  have [ident h] [":", expr ∀
   n : exprℕ(), «expr ↔ »(«expr = »(«expr ^ »(«expr * »(σ, τ), n), 1), «expr ∧ »(«expr = »(«expr ^ »(σ, n), 1), «expr = »(«expr ^ »(τ, n), 1)))] [":=", expr λ
   n, by rw ["[", expr hστ.commute.mul_pow, ",", expr disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n), "]"] []],
  exact [expr nat.dvd_antisymm hστ.commute.order_of_mul_dvd_lcm (nat.lcm_dvd (order_of_dvd_of_pow_eq_one ((h (order_of «expr * »(σ, τ))).mp (pow_order_of_eq_one «expr * »(σ, τ))).1) (order_of_dvd_of_pow_eq_one ((h (order_of «expr * »(σ, τ))).mp (pow_order_of_eq_one «expr * »(σ, τ))).2))]
end

theorem disjoint.extend_domain {α : Type _} {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) {σ τ : perm α}
  (h : Disjoint σ τ) : Disjoint (σ.extend_domain f) (τ.extend_domain f) :=
  by 
    intro b 
    byCases' pb : p b
    ·
      refine' (h (f.symm ⟨b, pb⟩)).imp _ _ <;>
        ·
          intro h 
          rw [extend_domain_apply_subtype _ _ pb, h, apply_symm_apply, Subtype.coe_mk]
    ·
      left 
      rw [extend_domain_apply_not_subtype _ _ pb]

variable [DecidableEq α]

section Fintype

variable [Fintype α]

theorem support_pow_coprime {σ : perm α} {n : ℕ} (h : Nat.Coprime n (orderOf σ)) : (σ ^ n).support = σ.support :=
  by 
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h 
    exact le_antisymmₓ (support_pow_le σ n) (le_transₓ (ge_of_eq (congr_argₓ support hm)) (support_pow_le (σ ^ n) m))

end Fintype

/-- Given a list `l : list α` and a permutation `f : perm α` such that the nonfixed points of `f`
  are in `l`, recursively factors `f` as a product of transpositions. -/
def swap_factors_aux :
  ∀ l : List α f : perm α, (∀ {x}, f x ≠ x → x ∈ l) → { l : List (perm α) // l.prod = f ∧ ∀ g _ : g ∈ l, is_swap g }
| [] =>
  fun f h =>
    ⟨[],
      Equiv.ext$
        fun x =>
          by 
            rw [List.prod_nil]
            exact (not_not.1 (mt h (List.not_mem_nil _))).symm,
      by 
        simp ⟩
| x :: l =>
  fun f h =>
    if hfx : x = f x then
      swap_factors_aux l f
        fun y hy =>
          List.mem_of_ne_of_memₓ
            (fun h : y = x =>
              by 
                simpa [h, hfx.symm] using hy)
            (h hy)
    else
      let m :=
        swap_factors_aux l (swap x (f x)*f)
          fun y hy =>
            have  : f y ≠ y ∧ y ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hy 
            List.mem_of_ne_of_memₓ this.2 (h this.1)
      ⟨swap x (f x) :: m.1,
        by 
          rw [List.prod_cons, m.2.1, ←mul_assocₓ, mul_def (swap x (f x)), swap_swap, ←one_def, one_mulₓ],
        fun g hg => ((List.mem_cons_iffₓ _ _ _).1 hg).elim (fun h => ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩

/-- `swap_factors` represents a permutation as a product of a list of transpositions.
The representation is non unique and depends on the linear order structure.
For types without linear order `trunc_swap_factors` can be used. -/
def swap_factors [Fintype α] [LinearOrderₓ α] (f : perm α) :
  { l : List (perm α) // l.prod = f ∧ ∀ g _ : g ∈ l, is_swap g } :=
  swap_factors_aux ((@univ α _).sort (· ≤ ·)) f fun _ _ => (mem_sort _).2 (mem_univ _)

/-- This computably represents the fact that any permutation can be represented as the product of
  a list of transpositions. -/
def trunc_swap_factors [Fintype α] (f : perm α) :
  Trunc { l : List (perm α) // l.prod = f ∧ ∀ g _ : g ∈ l, is_swap g } :=
  Quotientₓ.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (swap_factors_aux l f h))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_eliminator]
theorem swap_induction_on
[fintype α]
{P : perm α → exprProp()}
(f : perm α) : P 1 → ∀ f x y, «expr ≠ »(x, y) → P f → P «expr * »(swap x y, f) → P f :=
begin
  cases [expr (trunc_swap_factors f).out] ["with", ident l, ident hl],
  induction [expr l] [] ["with", ident g, ident l, ident ih] ["generalizing", ident f],
  { simp [] [] ["only"] ["[", expr hl.left.symm, ",", expr list.prod_nil, ",", expr forall_true_iff, "]"] [] [] { contextual := tt } },
  { assume [binders (h1 hmul_swap)],
    rcases [expr hl.2 g (by simp [] [] [] [] [] []), "with", "⟨", ident x, ",", ident y, ",", ident hxy, "⟩"],
    rw ["[", "<-", expr hl.1, ",", expr list.prod_cons, ",", expr hxy.2, "]"] [],
    exact [expr hmul_swap _ _ _ hxy.1 (ih _ ⟨rfl, λ v hv, hl.2 _ (list.mem_cons_of_mem _ hv)⟩ h1 hmul_swap)] }
end

theorem closure_is_swap [Fintype α] : Subgroup.closure { σ:perm α | is_swap σ } = ⊤ :=
  by 
    refine' eq_top_iff.mpr fun x hx => _ 
    obtain ⟨h1, h2⟩ := Subtype.mem (trunc_swap_factors x).out 
    rw [←h1]
    exact Subgroup.list_prod_mem _ fun y hy => Subgroup.subset_closure (h2 y hy)

/-- Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
@[elab_as_eliminator]
theorem swap_induction_on' [Fintype α] {P : perm α → Prop} (f : perm α) :
  P 1 → (∀ f x y, x ≠ y → P f → P (f*swap x y)) → P f :=
  fun h1 IH => inv_invₓ f ▸ swap_induction_on (f⁻¹) h1 fun f => IH (f⁻¹)

theorem is_conj_swap {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : IsConj (swap w x) (swap y z) :=
  is_conj_iff.2
    (have h : ∀ {y z : α}, y ≠ z → w ≠ z → (((swap w y*swap x z)*swap w x)*(swap w y*swap x z)⁻¹) = swap y z :=
      fun y z hyz hwz =>
        by 
          rw [mul_inv_rev, swap_inv, swap_inv, mul_assocₓ (swap w y), mul_assocₓ (swap w y), ←mul_assocₓ _ (swap x z),
            swap_mul_swap_mul_swap hwx hwz, ←mul_assocₓ, swap_mul_swap_mul_swap hwz.symm hyz.symm]
    if hwz : w = z then
      have hwy : w ≠ y :=
        by 
          cc
      ⟨swap w z*swap x y,
        by 
          rw [swap_comm y z, h hyz.symm hwy]⟩
    else ⟨swap w y*swap x z, h hyz hwz⟩)

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def fin_pairs_lt (n : ℕ) : Finset (Σa : Finₓ n, Finₓ n) :=
  (univ : Finset (Finₓ n)).Sigma fun a => (range a).attachFin fun m hm => (mem_range.1 hm).trans a.2

theorem mem_fin_pairs_lt {n : ℕ} {a : Σa : Finₓ n, Finₓ n} : a ∈ fin_pairs_lt n ↔ a.2 < a.1 :=
  by 
    simp only [fin_pairs_lt, Finₓ.lt_iff_coe_lt_coe, true_andₓ, mem_attach_fin, mem_range, mem_univ, mem_sigma]

/-- `sign_aux σ` is the sign of a permutation on `fin n`, defined as the parity of the number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂` -/
def sign_aux {n : ℕ} (a : perm (Finₓ n)) : Units ℤ :=
  ∏x in fin_pairs_lt n, if a x.1 ≤ a x.2 then -1 else 1

@[simp]
theorem sign_aux_one (n : ℕ) : sign_aux (1 : perm (Finₓ n)) = 1 :=
  by 
    unfold sign_aux 
    conv  => toRHS rw [←@Finset.prod_const_one (Units ℤ) _ (fin_pairs_lt n)]
    exact Finset.prod_congr rfl fun a ha => if_neg (mem_fin_pairs_lt.1 ha).not_le

/-- `sign_bij_aux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasing order. -/
def sign_bij_aux {n : ℕ} (f : perm (Finₓ n)) (a : Σa : Finₓ n, Finₓ n) : Σa : Finₓ n, Finₓ n :=
  if hxa : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sign_bij_aux_inj
{n : exprℕ()}
{f : perm (fin n)} : ∀
a
b : «exprΣ , »((a : fin n), fin n), «expr ∈ »(a, fin_pairs_lt n) → «expr ∈ »(b, fin_pairs_lt n) → «expr = »(sign_bij_aux f a, sign_bij_aux f b) → «expr = »(a, b) :=
λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ (ha hb h), begin
  unfold [ident sign_bij_aux] ["at", ident h],
  rw [expr mem_fin_pairs_lt] ["at", "*"],
  have [] [":", expr «expr¬ »(«expr < »(b₁, b₂))] [":=", expr hb.le.not_lt],
  split_ifs ["at", ident h] []; simp [] [] ["only"] ["[", "*", ",", expr (equiv.injective f).eq_iff, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr heq_iff_eq, "]"] [] ["at", "*"]
end

theorem sign_bij_aux_surj {n : ℕ} {f : perm (Finₓ n)} :
  ∀ a _ : a ∈ fin_pairs_lt n, ∃ (b : _)(_ : b ∈ fin_pairs_lt n), a = sign_bij_aux f b :=
  fun ⟨a₁, a₂⟩ ha =>
    if hxa : (f⁻¹) a₂ < (f⁻¹) a₁ then
      ⟨⟨(f⁻¹) a₁, (f⁻¹) a₂⟩, mem_fin_pairs_lt.2 hxa,
        by 
          dsimp [sign_bij_aux]
          rw [apply_inv_self, apply_inv_self, if_pos (mem_fin_pairs_lt.1 ha)]⟩
    else
      ⟨⟨(f⁻¹) a₂, (f⁻¹) a₁⟩,
        mem_fin_pairs_lt.2$
          (le_of_not_gtₓ hxa).lt_of_ne$
            fun h =>
              by 
                simpa [mem_fin_pairs_lt, f⁻¹.Injective h, lt_irreflₓ] using ha,
        by 
          dsimp [sign_bij_aux]
          rw [apply_inv_self, apply_inv_self, if_neg (mem_fin_pairs_lt.1 ha).le.not_lt]⟩

theorem sign_bij_aux_mem {n : ℕ} {f : perm (Finₓ n)} :
  ∀ a : Σa : Finₓ n, Finₓ n, a ∈ fin_pairs_lt n → sign_bij_aux f a ∈ fin_pairs_lt n :=
  fun ⟨a₁, a₂⟩ ha =>
    by 
      unfold sign_bij_aux 
      splitIfs with h
      ·
        exact mem_fin_pairs_lt.2 h
      ·
        exact mem_fin_pairs_lt.2 ((le_of_not_gtₓ h).lt_of_ne fun h => (mem_fin_pairs_lt.1 ha).Ne (f.injective h.symm))

@[simp]
theorem sign_aux_inv {n : ℕ} (f : perm (Finₓ n)) : sign_aux (f⁻¹) = sign_aux f :=
  prod_bij (fun a ha => sign_bij_aux (f⁻¹) a) sign_bij_aux_mem
    (fun ⟨a, b⟩ hab =>
      if h : (f⁻¹) b < (f⁻¹) a then
        by 
          rw [sign_bij_aux, dif_pos h, if_neg h.not_le, apply_inv_self, apply_inv_self,
            if_neg (mem_fin_pairs_lt.1 hab).not_le]
      else
        by 
          rw [sign_bij_aux, if_pos (le_of_not_gtₓ h), dif_neg h, apply_inv_self, apply_inv_self,
            if_pos (mem_fin_pairs_lt.1 hab).le])
    sign_bij_aux_inj sign_bij_aux_surj

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sign_aux_mul
{n : exprℕ()}
(f g : perm (fin n)) : «expr = »(sign_aux «expr * »(f, g), «expr * »(sign_aux f, sign_aux g)) :=
begin
  rw ["<-", expr sign_aux_inv g] [],
  unfold [ident sign_aux] [],
  rw ["<-", expr prod_mul_distrib] [],
  refine [expr prod_bij (λ a ha, sign_bij_aux g a) sign_bij_aux_mem _ sign_bij_aux_inj sign_bij_aux_surj],
  rintros ["⟨", ident a, ",", ident b, "⟩", ident hab],
  rw ["[", expr sign_bij_aux, ",", expr mul_apply, ",", expr mul_apply, "]"] [],
  rw [expr mem_fin_pairs_lt] ["at", ident hab],
  by_cases [expr h, ":", expr «expr < »(g b, g a)],
  { rw [expr dif_pos h] [],
    simp [] [] ["only"] ["[", expr not_le_of_gt hab, ",", expr mul_one, ",", expr perm.inv_apply_self, ",", expr if_false, "]"] [] [] },
  { rw ["[", expr dif_neg h, ",", expr inv_apply_self, ",", expr inv_apply_self, ",", expr if_pos hab.le, "]"] [],
    by_cases [expr h₁, ":", expr «expr ≤ »(f (g b), f (g a))],
    { have [] [":", expr «expr ≠ »(f (g b), f (g a))] [],
      { rw ["[", expr ne.def, ",", expr f.injective.eq_iff, ",", expr g.injective.eq_iff, "]"] [],
        exact [expr ne_of_lt hab] },
      rw ["[", expr if_pos h₁, ",", expr if_neg (h₁.lt_of_ne this).not_le, "]"] [],
      refl },
    { rw ["[", expr if_neg h₁, ",", expr if_pos (lt_of_not_ge h₁).le, "]"] [],
      refl } }
end

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem sign_aux_swap_zero_one' (n : exprℕ()) : «expr = »(sign_aux (swap (0 : fin «expr + »(n, 2)) 1), «expr- »(1)) :=
show «expr = »(_, «expr∏ in , »((x : «exprΣ , »((a : fin «expr + »(n, 2)), fin «expr + »(n, 2))), {(⟨1, 0⟩ : «exprΣ , »((a : fin «expr + »(n, 2)), fin «expr + »(n, 2)))}, if «expr ≤ »(equiv.swap 0 1 x.1, swap 0 1 x.2) then («expr- »(1) : units exprℤ()) else 1)), begin
  refine [expr eq.symm (prod_subset (λ
     ⟨x₁, x₂⟩, by simp [] [] [] ["[", expr mem_fin_pairs_lt, ",", expr fin.one_pos, "]"] [] [] { contextual := tt }) (λ
     a ha₁ ha₂, _))],
  rcases [expr a, "with", "⟨", ident a₁, ",", ident a₂, "⟩"],
  replace [ident ha₁] [":", expr «expr < »(a₂, a₁)] [":=", expr mem_fin_pairs_lt.1 ha₁],
  dsimp ["only"] [] [] [],
  rcases [expr a₁.zero_le.eq_or_lt, "with", ident rfl, "|", ident H],
  { exact [expr absurd a₂.zero_le ha₁.not_le] },
  rcases [expr a₂.zero_le.eq_or_lt, "with", ident rfl, "|", ident H'],
  { simp [] [] ["only"] ["[", expr and_true, ",", expr eq_self_iff_true, ",", expr heq_iff_eq, ",", expr mem_singleton, "]"] [] ["at", ident ha₂],
    have [] [":", expr «expr < »(1, a₁)] [":=", expr lt_of_le_of_ne (nat.succ_le_of_lt ha₁) (ne.symm ha₂)],
    have [ident h01] [":", expr «expr = »(equiv.swap (0 : fin «expr + »(n, 2)) 1 0, 1)] [],
    by simp [] [] [] [] [] [],
    norm_num ["[", expr swap_apply_of_ne_of_ne (ne_of_gt H) ha₂, ",", expr this.not_le, ",", expr h01, "]"] [] },
  { have [ident le] [":", expr «expr ≤ »(1, a₂)] [":=", expr nat.succ_le_of_lt H'],
    have [ident lt] [":", expr «expr < »(1, a₁)] [":=", expr le.trans_lt ha₁],
    have [ident h01] [":", expr «expr = »(equiv.swap (0 : fin «expr + »(n, 2)) 1 1, 0)] [],
    by simp [] [] [] [] [] [],
    rcases [expr le.eq_or_lt, "with", ident rfl, "|", ident lt'],
    { norm_num ["[", expr swap_apply_of_ne_of_ne H.ne' lt.ne', ",", expr H.not_le, ",", expr h01, "]"] [] },
    { norm_num ["[", expr swap_apply_of_ne_of_ne (ne_of_gt H) (ne_of_gt lt), ",", expr swap_apply_of_ne_of_ne (ne_of_gt H') (ne_of_gt lt'), ",", expr ha₁.not_le, "]"] [] } }
end

private theorem sign_aux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
  sign_aux
      (swap
        (⟨0,
          lt_of_lt_of_leₓ
            (by 
              decide)
            hn⟩ :
        Finₓ n)
        ⟨1,
          lt_of_lt_of_leₓ
            (by 
              decide)
            hn⟩) =
    -1 :=
  by 
    rcases n with (_ | _ | n)
    ·
      normNum  at hn
    ·
      normNum  at hn
    ·
      exact sign_aux_swap_zero_one' n

theorem sign_aux_swap : ∀ {n : ℕ} {x y : Finₓ n} hxy : x ≠ y, sign_aux (swap x y) = -1
| 0 =>
  by 
    decide
| 1 =>
  by 
    decide
| n+2 =>
  fun x y hxy =>
    have h2n : 2 ≤ n+2 :=
      by 
        decide 
    by 
      rw [←is_conj_iff_eq, ←sign_aux_swap_zero_one h2n]
      exact
        (MonoidHom.mk' sign_aux sign_aux_mul).map_is_conj
          (is_conj_swap hxy
            (by 
              decide))

/-- When the list `l : list α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 l f` recursively calculates the sign of `f`. -/
def sign_aux2 : List α → perm α → Units ℤ
| [], f => 1
| x :: l, f => if x = f x then sign_aux2 l f else -sign_aux2 l (swap x (f x)*f)

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sign_aux_eq_sign_aux2
{n : exprℕ()} : ∀
(l : list α)
(f : perm α)
(e : «expr ≃ »(α, fin n))
(h : ∀ x, «expr ≠ »(f x, x) → «expr ∈ »(x, l)), «expr = »(sign_aux ((e.symm.trans f).trans e), sign_aux2 l f)
| «expr[ , ]»([]), f, e, h := have «expr = »(f, 1), from «expr $ »(equiv.ext, λ
 y, not_not.1 (mt (h y) (list.not_mem_nil _))),
by rw ["[", expr this, ",", expr one_def, ",", expr equiv.trans_refl, ",", expr equiv.symm_trans_self, ",", "<-", expr one_def, ",", expr sign_aux_one, ",", expr sign_aux2, "]"] []
| [«expr :: »/«expr :: »/«expr :: »](x, l), f, e, h := begin
  rw [expr sign_aux2] [],
  by_cases [expr hfx, ":", expr «expr = »(x, f x)],
  { rw [expr if_pos hfx] [],
    exact [expr sign_aux_eq_sign_aux2 l f _ (λ
      (y)
      (hy : «expr ≠ »(f y, y)), list.mem_of_ne_of_mem (λ
       h : «expr = »(y, x), by simpa [] [] [] ["[", expr h, ",", expr hfx.symm, "]"] [] ["using", expr hy]) (h y hy))] },
  { have [ident hy] [":", expr ∀ y : α, «expr ≠ »(«expr * »(swap x (f x), f) y, y) → «expr ∈ »(y, l)] [],
    from [expr λ y hy, have «expr ∧ »(«expr ≠ »(f y, y), «expr ≠ »(y, x)), from ne_and_ne_of_swap_mul_apply_ne_self hy,
     list.mem_of_ne_of_mem this.2 (h _ this.1)],
    have [] [":", expr «expr = »((e.symm.trans «expr * »(swap x (f x), f)).trans e, «expr * »(swap (e x) (e (f x)), (e.symm.trans f).trans e))] [],
    by ext [] [] []; simp [] [] [] ["[", "<-", expr equiv.symm_trans_swap_trans, ",", expr mul_def, "]"] [] [],
    have [ident hefx] [":", expr «expr ≠ »(e x, e (f x))] [],
    from [expr mt e.injective.eq_iff.1 hfx],
    rw ["[", expr if_neg hfx, ",", "<-", expr sign_aux_eq_sign_aux2 _ _ e hy, ",", expr this, ",", expr sign_aux_mul, ",", expr sign_aux_swap hefx, "]"] [],
    simp [] [] ["only"] ["[", expr units.neg_neg, ",", expr one_mul, ",", expr units.neg_mul, "]"] [] [] }
end

/-- When the multiset `s : multiset α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 f _` recursively calculates the sign of `f`. -/
def sign_aux3 [Fintype α] (f : perm α) {s : Multiset α} : (∀ x, x ∈ s) → Units ℤ :=
  Quotientₓ.hrecOn s (fun l h => sign_aux2 l f)
    (Trunc.induction_on (Fintype.truncEquivFin α)
      fun e l₁ l₂ h =>
        Function.hfunext
          (show (∀ x, x ∈ l₁) = ∀ x, x ∈ l₂ by 
            simp only [h.mem_iff])
          fun h₁ h₂ _ =>
            by 
              rw [←sign_aux_eq_sign_aux2 _ _ e fun _ _ => h₁ _, ←sign_aux_eq_sign_aux2 _ _ e fun _ _ => h₂ _])

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sign_aux3_mul_and_swap
[fintype α]
(f g : perm α)
(s : multiset α)
(hs : ∀
 x, «expr ∈ »(x, s)) : «expr ∧ »(«expr = »(sign_aux3 «expr * »(f, g) hs, «expr * »(sign_aux3 f hs, sign_aux3 g hs)), ∀
 x y, «expr ≠ »(x, y) → «expr = »(sign_aux3 (swap x y) hs, «expr- »(1))) :=
let ⟨l, hl⟩ := quotient.exists_rep s in
let e := equiv_fin α in
begin
  clear [ident _let_match],
  subst [expr hl],
  show [expr «expr ∧ »(«expr = »(sign_aux2 l «expr * »(f, g), «expr * »(sign_aux2 l f, sign_aux2 l g)), ∀
    x y, «expr ≠ »(x, y) → «expr = »(sign_aux2 l (swap x y), «expr- »(1)))],
  have [ident hfg] [":", expr «expr = »((e.symm.trans «expr * »(f, g)).trans e, «expr * »((e.symm.trans f).trans e, (e.symm.trans g).trans e))] [],
  from [expr equiv.ext (λ h, by simp [] [] [] ["[", expr mul_apply, "]"] [] [])],
  split,
  { rw ["[", "<-", expr sign_aux_eq_sign_aux2 _ _ e (λ
      _
      _, hs _), ",", "<-", expr sign_aux_eq_sign_aux2 _ _ e (λ
      _
      _, hs _), ",", "<-", expr sign_aux_eq_sign_aux2 _ _ e (λ
      _ _, hs _), ",", expr hfg, ",", expr sign_aux_mul, "]"] [] },
  { assume [binders (x y hxy)],
    have [ident hexy] [":", expr «expr ≠ »(e x, e y)] [],
    from [expr mt e.injective.eq_iff.1 hxy],
    rw ["[", "<-", expr sign_aux_eq_sign_aux2 _ _ e (λ
      _ _, hs _), ",", expr symm_trans_swap_trans, ",", expr sign_aux_swap hexy, "]"] [] }
end

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`perm α` to the group with two elements.-/
def sign [Fintype α] : perm α →* Units ℤ :=
  MonoidHom.mk' (fun f => sign_aux3 f mem_univ) fun f g => (sign_aux3_mul_and_swap f g _ mem_univ).1

section Sign

variable [Fintype α]

@[simp]
theorem sign_mul (f g : perm α) : sign (f*g) = sign f*sign g :=
  MonoidHom.map_mul sign f g

@[simp]
theorem sign_trans (f g : perm α) : sign (f.trans g) = sign g*sign f :=
  by 
    rw [←mul_def, sign_mul]

@[simp]
theorem sign_one : sign (1 : perm α) = 1 :=
  MonoidHom.map_one sign

@[simp]
theorem sign_refl : sign (Equiv.refl α) = 1 :=
  MonoidHom.map_one sign

@[simp]
theorem sign_inv (f : perm α) : sign (f⁻¹) = sign f :=
  by 
    rw [MonoidHom.map_inv sign f, Int.units_inv_eq_self]

@[simp]
theorem sign_symm (e : perm α) : sign e.symm = sign e :=
  sign_inv e

theorem sign_swap {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
  (sign_aux3_mul_and_swap 1 1 _ mem_univ).2 x y h

@[simp]
theorem sign_swap' {x y : α} : (swap x y).sign = if x = y then 1 else -1 :=
  if H : x = y then
    by 
      simp [H, swap_self]
  else
    by 
      simp [sign_swap H, H]

theorem is_swap.sign_eq {f : perm α} (h : f.is_swap) : sign f = -1 :=
  let ⟨x, y, hxy⟩ := h 
  hxy.2.symm ▸ sign_swap hxy.1

theorem sign_aux3_symm_trans_trans [DecidableEq β] [Fintype β] (f : perm α) (e : α ≃ β) {s : Multiset α}
  {t : Multiset β} (hs : ∀ x, x ∈ s) (ht : ∀ x, x ∈ t) : sign_aux3 ((e.symm.trans f).trans e) ht = sign_aux3 f hs :=
  Quotientₓ.induction_on₂ t s
    (fun l₁ l₂ h₁ h₂ =>
      show sign_aux2 _ _ = sign_aux2 _ _ from
        let n := equiv_fin β 
        by 
          rw [←sign_aux_eq_sign_aux2 _ _ n fun _ _ => h₁ _, ←sign_aux_eq_sign_aux2 _ _ (e.trans n) fun _ _ => h₂ _]
          exact
            congr_argₓ sign_aux
              (Equiv.ext
                fun x =>
                  by 
                    simp only [Equiv.coe_trans, apply_eq_iff_eq, symm_trans_apply]))
    ht hs

@[simp]
theorem sign_symm_trans_trans [DecidableEq β] [Fintype β] (f : perm α) (e : α ≃ β) :
  sign ((e.symm.trans f).trans e) = sign f :=
  sign_aux3_symm_trans_trans f e mem_univ mem_univ

@[simp]
theorem sign_trans_trans_symm [DecidableEq β] [Fintype β] (f : perm β) (e : α ≃ β) :
  sign ((e.trans f).trans e.symm) = sign f :=
  sign_symm_trans_trans f e.symm

theorem sign_prod_list_swap {l : List (perm α)} (hl : ∀ g _ : g ∈ l, is_swap g) : sign l.prod = -1 ^ l.length :=
  have h₁ : l.map sign = List.repeat (-1) l.length :=
    List.eq_repeat.2
      ⟨by 
          simp ,
        fun u hu =>
          let ⟨g, hg⟩ := List.mem_mapₓ.1 hu 
          hg.2 ▸ (hl _ hg.1).sign_eq⟩
  by 
    rw [←List.prod_repeat, ←h₁, List.prod_hom _ (@sign α _ _)]

variable (α)

theorem sign_surjective [Nontrivial α] : Function.Surjective (sign : perm α → Units ℤ) :=
  fun a =>
    (Int.units_eq_one_or a).elim
      (fun h =>
        ⟨1,
          by 
            simp [h]⟩)
      fun h =>
        let ⟨x, y, hxy⟩ := exists_pair_ne α
        ⟨swap x y,
          by 
            rw [sign_swap hxy, h]⟩

variable {α}

theorem eq_sign_of_surjective_hom {s : perm α →* Units ℤ} (hs : surjective s) : s = sign :=
  have  : ∀ {f}, is_swap f → s f = -1 :=
    fun f ⟨x, y, hxy, hxy'⟩ =>
      hxy'.symm ▸
        by_contradiction
          fun h =>
            have  : ∀ f, is_swap f → s f = 1 :=
              fun f ⟨a, b, hab, hab'⟩ =>
                by 
                  rw [←is_conj_iff_eq, ←Or.resolve_right (Int.units_eq_one_or _) h, hab']
                  exact s.map_is_conj (is_conj_swap hab hxy)
            let ⟨g, hg⟩ := hs (-1)
            let ⟨l, hl⟩ := (trunc_swap_factors g).out 
            have  : ∀ a _ : a ∈ l.map s, a = (1 : Units ℤ) :=
              fun a ha =>
                let ⟨g, hg⟩ := List.mem_mapₓ.1 ha 
                hg.2 ▸ this _ (hl.2 _ hg.1)
            have  : s l.prod = 1 :=
              by 
                rw [←l.prod_hom s, List.eq_repeat'.2 this, List.prod_repeat, one_pow]
            by 
              rw [hl.1, hg] at this 
              exact
                absurd this
                  (by 
                    decide)
  MonoidHom.ext$
    fun f =>
      let ⟨l, hl₁, hl₂⟩ := (trunc_swap_factors f).out 
      have hsl : ∀ a _ : a ∈ l.map s, a = (-1 : Units ℤ) :=
        fun a ha =>
          let ⟨g, hg⟩ := List.mem_mapₓ.1 ha 
          hg.2 ▸ this (hl₂ _ hg.1)
      by 
        rw [←hl₁, ←l.prod_hom s, List.eq_repeat'.2 hsl, List.length_map, List.prod_repeat, sign_prod_list_swap hl₂]

theorem sign_subtype_perm (f : perm α) {p : α → Prop} [DecidablePred p] (h₁ : ∀ x, p x ↔ p (f x))
  (h₂ : ∀ x, f x ≠ x → p x) : sign (subtype_perm f h₁) = sign f :=
  let l := (trunc_swap_factors (subtype_perm f h₁)).out 
  have hl' : ∀ g' _ : g' ∈ l.1.map of_subtype, is_swap g' :=
    fun g' hg' =>
      let ⟨g, hg⟩ := List.mem_mapₓ.1 hg' 
      hg.2 ▸ (l.2.2 _ hg.1).of_subtype_is_swap 
  have hl'₂ : (l.1.map of_subtype).Prod = f :=
    by 
      rw [l.1.prod_hom of_subtype, l.2.1, of_subtype_subtype_perm _ h₂]
  by 
    conv  => congr rw [←l.2.1]skip rw [←hl'₂]
    rw [sign_prod_list_swap l.2.2, sign_prod_list_swap hl', List.length_map]

@[simp]
theorem sign_of_subtype {p : α → Prop} [DecidablePred p] (f : perm (Subtype p)) : sign (of_subtype f) = sign f :=
  have  : ∀ x, of_subtype f x ≠ x → p x := fun x => not_imp_comm.1 (of_subtype_apply_of_not_mem f)
  by 
    conv  => toRHS rw [←subtype_perm_of_subtype f, sign_subtype_perm _ _ this]

theorem sign_eq_sign_of_equiv [DecidableEq β] [Fintype β] (f : perm α) (g : perm β) (e : α ≃ β)
  (h : ∀ x, e (f x) = g (e x)) : sign f = sign g :=
  have hg : g = (e.symm.trans f).trans e :=
    Equiv.ext$
      by 
        simp [h]
  by 
    rw [hg, sign_symm_trans_trans]

theorem sign_bij [DecidableEq β] [Fintype β] {f : perm α} {g : perm β} (i : ∀ x : α, f x ≠ x → β)
  (h : ∀ x hx hx', i (f x) hx' = g (i x hx)) (hi : ∀ x₁ x₂ hx₁ hx₂, i x₁ hx₁ = i x₂ hx₂ → x₁ = x₂)
  (hg : ∀ y, g y ≠ y → ∃ x hx, i x hx = y) : sign f = sign g :=
  calc
    sign f =
      sign
        (@subtype_perm _ f (fun x => f x ≠ x)
          (by 
            simp )) :=
    (sign_subtype_perm _ _ fun _ => id).symm 
    _ =
      sign
        (@subtype_perm _ g (fun x => g x ≠ x)
          (by 
            simp )) :=
    sign_eq_sign_of_equiv _ _
      (Equiv.ofBijective
        (fun x : { x // f x ≠ x } =>
          (⟨i x.1 x.2,
            have  : f (f x) ≠ f x := mt (fun h => f.injective h) x.2
            by 
              rw [←h _ x.2 this]
              exact mt (hi _ _ this x.2) x.2⟩ :
          { y // g y ≠ y }))
        ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ h => Subtype.eq (hi _ _ _ _ (Subtype.mk.injₓ h)),
          fun ⟨y, hy⟩ =>
            let ⟨x, hfx, hx⟩ := hg y hy
            ⟨⟨x, hfx⟩, Subtype.eq hx⟩⟩)
      fun ⟨x, _⟩ => Subtype.eq (h x _ _)
    _ = sign g := sign_subtype_perm _ _ fun _ => id
    

/-- If we apply `prod_extend_right a (σ a)` for all `a : α` in turn,
we get `prod_congr_right σ`. -/
theorem prod_prod_extend_right {α : Type _} [DecidableEq α] (σ : α → perm β) {l : List α} (hl : l.nodup)
  (mem_l : ∀ a, a ∈ l) : (l.map fun a => prod_extend_right a (σ a)).Prod = prod_congr_right σ :=
  by 
    ext ⟨a, b⟩ : 1
    suffices  :
      a ∈ l ∧ (l.map fun a => prod_extend_right a (σ a)).Prod (a, b) = (a, σ a b) ∨
        a ∉ l ∧ (l.map fun a => prod_extend_right a (σ a)).Prod (a, b) = (a, b)
    ·
      obtain ⟨_, prod_eq⟩ := Or.resolve_right this (not_and.mpr fun h _ => h (mem_l a))
      rw [prod_eq, prod_congr_right_apply]
    clear mem_l 
    induction' l with a' l ih
    ·
      refine' Or.inr ⟨List.not_mem_nil _, _⟩
      rw [List.map_nil, List.prod_nil, one_apply]
    rw [List.map_consₓ, List.prod_cons, mul_apply]
    rcases ih (list.nodup_cons.mp hl).2 with (⟨mem_l, prod_eq⟩ | ⟨not_mem_l, prod_eq⟩) <;> rw [prod_eq]
    ·
      refine' Or.inl ⟨List.mem_cons_of_memₓ _ mem_l, _⟩
      rw [prod_extend_right_apply_ne _ fun h : a = a' => (list.nodup_cons.mp hl).1 (h ▸ mem_l)]
    byCases' ha' : a = a'
    ·
      rw [←ha'] at *
      refine' Or.inl ⟨l.mem_cons_self a, _⟩
      rw [prod_extend_right_apply_eq]
    ·
      refine' Or.inr ⟨fun h => not_orₓ ha' not_mem_l ((List.mem_cons_iffₓ _ _ _).mp h), _⟩
      rw [prod_extend_right_apply_ne _ ha']

section congr

variable [DecidableEq β] [Fintype β]

@[simp]
theorem sign_prod_extend_right (a : α) (σ : perm β) : (prod_extend_right a σ).sign = σ.sign :=
  sign_bij (fun ab : α × β _ => ab.snd)
    (fun ⟨a', b⟩ hab hab' =>
      by 
        simp [eq_of_prod_extend_right_ne hab])
    (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab₁ hab₂ h =>
      by 
        simpa [eq_of_prod_extend_right_ne hab₁, eq_of_prod_extend_right_ne hab₂] using h)
    fun y hy =>
      ⟨(a, y),
        by 
          simpa,
        by 
          simp ⟩

-- error in GroupTheory.Perm.Sign: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sign_prod_congr_right (σ : α → perm β) : «expr = »(sign (prod_congr_right σ), «expr∏ , »((k), (σ k).sign)) :=
begin
  obtain ["⟨", ident l, ",", ident hl, ",", ident mem_l, "⟩", ":=", expr fintype.exists_univ_list α],
  have [ident l_to_finset] [":", expr «expr = »(l.to_finset, finset.univ)] [],
  { apply [expr eq_top_iff.mpr],
    intros [ident b, "_"],
    exact [expr list.mem_to_finset.mpr (mem_l b)] },
  rw ["[", "<-", expr prod_prod_extend_right σ hl mem_l, ",", expr sign.map_list_prod, ",", expr list.map_map, ",", "<-", expr l_to_finset, ",", expr list.prod_to_finset _ hl, "]"] [],
  simp_rw ["<-", expr λ a, sign_prod_extend_right a (σ a)] []
end

theorem sign_prod_congr_left (σ : α → perm β) : sign (prod_congr_left σ) = ∏k, (σ k).sign :=
  by 
    refine' (sign_eq_sign_of_equiv _ _ (prod_comm β α) _).trans (sign_prod_congr_right σ)
    rintro ⟨b, α⟩
    rfl

@[simp]
theorem sign_perm_congr (e : α ≃ β) (p : perm α) : (e.perm_congr p).sign = p.sign :=
  sign_eq_sign_of_equiv _ _ e.symm
    (by 
      simp )

@[simp]
theorem sign_sum_congr (σa : perm α) (σb : perm β) : (sum_congr σa σb).sign = σa.sign*σb.sign :=
  by 
    suffices  : (sum_congr σa (1 : perm β)).sign = σa.sign ∧ (sum_congr (1 : perm α) σb).sign = σb.sign
    ·
      rw [←this.1, ←this.2, ←sign_mul, sum_congr_mul, one_mulₓ, mul_oneₓ]
    split 
    ·
      apply σa.swap_induction_on _ fun σa' a₁ a₂ ha ih => _
      ·
        simp 
      ·
        rw [←one_mulₓ (1 : perm β), ←sum_congr_mul, sign_mul, sign_mul, ih, sum_congr_swap_one, sign_swap ha,
          sign_swap (sum.inl_injective.ne_iff.mpr ha)]
    ·
      apply σb.swap_induction_on _ fun σb' b₁ b₂ hb ih => _
      ·
        simp 
      ·
        rw [←one_mulₓ (1 : perm α), ←sum_congr_mul, sign_mul, sign_mul, ih, sum_congr_one_swap, sign_swap hb,
          sign_swap (sum.inr_injective.ne_iff.mpr hb)]

@[simp]
theorem sign_subtype_congr {p : α → Prop} [DecidablePred p] (ep : perm { a // p a }) (en : perm { a // ¬p a }) :
  (ep.subtype_congr en).sign = ep.sign*en.sign :=
  by 
    simp [subtype_congr]

@[simp]
theorem sign_extend_domain (e : perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
  Equiv.Perm.sign (e.extend_domain f) = Equiv.Perm.sign e :=
  by 
    simp [Equiv.Perm.extendDomain]

end congr

end Sign

end Equiv.Perm

