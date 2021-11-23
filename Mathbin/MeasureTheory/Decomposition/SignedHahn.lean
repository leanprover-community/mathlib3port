import Mathbin.MeasureTheory.Measure.VectorMeasure 
import Mathbin.Order.SymmDiff

/-!
# Hahn decomposition

This file prove the Hahn decomposition theorem (signed version). The Hahn decomposition theorem
states that, given a signed measure `s`, there exist complement, measurable sets `i` and `j`,
such that `i` is positive and `j` is negative with repsect to `s`; that is, `s` restricted on `i`
is non-negative and `s` restricted on `j` is non-positive.

The Hahn decomposition theorem leads to many other results in measure theory, most notably,
the Jordan decomposition theorem, the Lebesgue decomposition theorem and the Radon-Nikodym theorem.

## Main results

* `measure_theory.signed_measure.exists_is_compl_positive_negative` : the Hahn decomposition
  theorem.
* `measure_theory.signed_measure.exists_subset_restrict_nonpos` : A measurable set of negative
  measure contains a negative subset.

## Notation

We use the notations `0 ≤[i] s` and `s ≤[i] 0` to denote the usual definitions of a set `i`
being positive/negative with respect to the signed measure `s`.

## Tags

Hahn decomposition theorem
-/


noncomputable theory

open_locale Classical BigOperators Nnreal Ennreal MeasureTheory

variable{α β : Type _}[MeasurableSpace α]

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M][OrderedAddCommMonoid M]

namespace MeasureTheory

namespace SignedMeasure

open Filter VectorMeasure

variable{s : signed_measure α}{i j : Set α}

section ExistsSubsetRestrictNonpos

/-! ### exists_subset_restrict_nonpos

In this section we will prove that a set `i` whose measure is negative contains a negative subset
`j` with respect to the signed measure `s` (i.e. `s ≤[j] 0`), whose measure is negative. This lemma
is used to prove the Hahn decomposition theorem.

To prove this lemma, we will construct a sequence of measurable sets $(A_n)_{n \in \mathbb{N}}$,
such that, for all $n$, $s(A_{n + 1})$ is close to maximal among subsets of
$i \setminus \bigcup_{k \le n} A_k$.

This sequence of sets does not necessarily exist. However, if this sequence terminates; that is,
there does not exists any sets satisfying the property, the last $A_n$ will be a negative subset
of negative measure, hence proving our claim.

In the case that the sequence does not terminate, it is easy to see that
$i \setminus \bigcup_{k = 0}^\infty A_k$ is the required negative set.

To implement this in Lean, we define several auxilary definitions.

- given the sets `i` and the natural number `n`, `exists_one_div_lt s i n` is the property that
  there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`.
- given the sets `i` and that `i` is not negative, `find_exists_one_div_lt s i` is the
  least natural number `n` such that `exists_one_div_lt s i n`.
- given the sets `i` and that `i` is not negative, `some_exists_one_div_lt` chooses the set
  `k` from `exists_one_div_lt s i (find_exists_one_div_lt s i)`.
- lastly, given the set `i`, `restrict_nonpos_seq s i` is the sequence of sets defined inductively
  where
  `restrict_nonpos_seq s i 0 = some_exists_one_div_lt s (i \ ∅)` and
  `restrict_nonpos_seq s i (n + 1) = some_exists_one_div_lt s (i \ ⋃ k ≤ n, restrict_nonpos_seq k)`.
  This definition represents the sequence $(A_n)$ in the proof as described above.

With these definitions, we are able consider the case where the sequence terminates separately,
allowing us to prove `exists_subset_restrict_nonpos`.
-/


/-- Given the set `i` and the natural number `n`, `exists_one_div_lt s i j` is the property that
there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`. -/
private def exists_one_div_lt (s : signed_measure α) (i : Set α) (n : ℕ) : Prop :=
  ∃ k : Set α, k ⊆ i ∧ MeasurableSet k ∧ (1 / n+1 : ℝ) < s k

private theorem exists_nat_one_div_lt_measure_of_not_negative (hi : ¬s ≤[i] 0) : ∃ n : ℕ, exists_one_div_lt s i n :=
  let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi 
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩

/-- Given the set `i`, if `i` is not negative, `find_exists_one_div_lt s i` is the
least natural number `n` such that `exists_one_div_lt s i n`, otherwise, it returns 0. -/
private def find_exists_one_div_lt (s : signed_measure α) (i : Set α) : ℕ :=
  if hi : ¬s ≤[i] 0 then Nat.findₓ (exists_nat_one_div_lt_measure_of_not_negative hi) else 0

private theorem find_exists_one_div_lt_spec (hi : ¬s ≤[i] 0) : exists_one_div_lt s i (find_exists_one_div_lt s i) :=
  by 
    rw [find_exists_one_div_lt, dif_pos hi]
    convert Nat.find_specₓ _

private theorem find_exists_one_div_lt_min (hi : ¬s ≤[i] 0) {m : ℕ} (hm : m < find_exists_one_div_lt s i) :
  ¬exists_one_div_lt s i m :=
  by 
    rw [find_exists_one_div_lt, dif_pos hi] at hm 
    exact Nat.find_minₓ _ hm

/-- Given the set `i`, if `i` is not negative, `some_exists_one_div_lt` chooses the set
`k` from `exists_one_div_lt s i (find_exists_one_div_lt s i)`, otherwise, it returns the
empty set. -/
private def some_exists_one_div_lt (s : signed_measure α) (i : Set α) : Set α :=
  if hi : ¬s ≤[i] 0 then Classical.some (find_exists_one_div_lt_spec hi) else ∅

private theorem some_exists_one_div_lt_spec (hi : ¬s ≤[i] 0) :
  some_exists_one_div_lt s i ⊆ i ∧
    MeasurableSet (some_exists_one_div_lt s i) ∧
      (1 / find_exists_one_div_lt s i+1 : ℝ) < s (some_exists_one_div_lt s i) :=
  by 
    rw [some_exists_one_div_lt, dif_pos hi]
    exact Classical.some_spec (find_exists_one_div_lt_spec hi)

private theorem some_exists_one_div_lt_subset : some_exists_one_div_lt s i ⊆ i :=
  by 
    byCases' hi : ¬s ≤[i] 0
    ·
      exact
        let ⟨h, _⟩ := some_exists_one_div_lt_spec hi 
        h
    ·
      rw [some_exists_one_div_lt, dif_neg hi]
      exact Set.empty_subset _

private theorem some_exists_one_div_lt_subset' : some_exists_one_div_lt s (i \ j) ⊆ i :=
  Set.Subset.trans some_exists_one_div_lt_subset (Set.diff_subset _ _)

private theorem some_exists_one_div_lt_measurable_set : MeasurableSet (some_exists_one_div_lt s i) :=
  by 
    byCases' hi : ¬s ≤[i] 0
    ·
      exact
        let ⟨_, h, _⟩ := some_exists_one_div_lt_spec hi 
        h
    ·
      rw [some_exists_one_div_lt, dif_neg hi]
      exact MeasurableSet.empty

private theorem some_exists_one_div_lt_lt (hi : ¬s ≤[i] 0) :
  (1 / find_exists_one_div_lt s i+1 : ℝ) < s (some_exists_one_div_lt s i) :=
  let ⟨_, _, h⟩ := some_exists_one_div_lt_spec hi 
  h

/-- Given the set `i`, `restrict_nonpos_seq s i` is the sequence of sets defined inductively where
`restrict_nonpos_seq s i 0 = some_exists_one_div_lt s (i \ ∅)` and
`restrict_nonpos_seq s i (n + 1) = some_exists_one_div_lt s (i \ ⋃ k ≤ n, restrict_nonpos_seq k)`.

For each `n : ℕ`,`s (restrict_nonpos_seq s i n)` is close to maximal among all subsets of
`i \ ⋃ k ≤ n, restrict_nonpos_seq s i k`. -/
private def restrict_nonpos_seq (s : signed_measure α) (i : Set α) : ℕ → Set α
| 0 => some_exists_one_div_lt s (i \ ∅)
| n+1 =>
  some_exists_one_div_lt s
    (i \
      ⋃(k : _)(_ : k ≤ n),
        have  : k < n+1 := Nat.lt_succ_iff.mpr H 
        restrict_nonpos_seq k)

private theorem restrict_nonpos_seq_succ (n : ℕ) :
  restrict_nonpos_seq s i n.succ = some_exists_one_div_lt s (i \ ⋃(k : _)(_ : k ≤ n), restrict_nonpos_seq s i k) :=
  by 
    rw [restrict_nonpos_seq]

private theorem restrict_nonpos_seq_subset (n : ℕ) : restrict_nonpos_seq s i n ⊆ i :=
  by 
    cases n <;>
      ·
        rw [restrict_nonpos_seq]
        exact some_exists_one_div_lt_subset'

private theorem restrict_nonpos_seq_lt (n : ℕ) (hn : ¬s ≤[i \ ⋃(k : _)(_ : k ≤ n), restrict_nonpos_seq s i k] 0) :
  (1 / find_exists_one_div_lt s (i \ ⋃(k : _)(_ : k ≤ n), restrict_nonpos_seq s i k)+1 : ℝ) <
    s (restrict_nonpos_seq s i n.succ) :=
  by 
    rw [restrict_nonpos_seq_succ]
    apply some_exists_one_div_lt_lt hn

-- error in MeasureTheory.Decomposition.SignedHahn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem measure_of_restrict_nonpos_seq
(hi₂ : «expr¬ »(«expr ≤[ ] »(s, i, 0)))
(n : exprℕ())
(hn : «expr¬ »(«expr ≤[ ] »(s, «expr \ »(i, «expr⋃ , »((k «expr < » n), restrict_nonpos_seq s i k)), 0))) : «expr < »(0, s (restrict_nonpos_seq s i n)) :=
begin
  cases [expr n] [],
  { rw [expr restrict_nonpos_seq] [],
    rw ["<-", expr @set.diff_empty _ i] ["at", ident hi₂],
    rcases [expr some_exists_one_div_lt_spec hi₂, "with", "⟨", "_", ",", "_", ",", ident h, "⟩"],
    exact [expr lt_trans nat.one_div_pos_of_nat h] },
  { rw [expr restrict_nonpos_seq_succ] [],
    have [ident h₁] [":", expr «expr¬ »(«expr ≤[ ] »(s, «expr \ »(i, «expr⋃ , »((k : exprℕ())
         (H : «expr ≤ »(k, n)), restrict_nonpos_seq s i k)), 0))] [],
    { refine [expr mt (restrict_le_zero_subset _ _ (by simp [] [] [] ["[", expr nat.lt_succ_iff, "]"] [] [])) hn],
      convert [] [expr measurable_of_not_restrict_le_zero _ hn] [],
      exact [expr funext (λ x, by rw [expr nat.lt_succ_iff] [])] },
    rcases [expr some_exists_one_div_lt_spec h₁, "with", "⟨", "_", ",", "_", ",", ident h, "⟩"],
    exact [expr lt_trans nat.one_div_pos_of_nat h] }
end

private theorem restrict_nonpos_seq_measurable_set (n : ℕ) : MeasurableSet (restrict_nonpos_seq s i n) :=
  by 
    cases n <;>
      ·
        rw [restrict_nonpos_seq]
        exact some_exists_one_div_lt_measurable_set

private theorem restrict_nonpos_seq_disjoint' {n m : ℕ} (h : n < m) :
  restrict_nonpos_seq s i n ∩ restrict_nonpos_seq s i m = ∅ :=
  by 
    rw [Set.eq_empty_iff_forall_not_mem]
    rintro x ⟨hx₁, hx₂⟩
    cases m
    ·
      linarith
    ·
      rw [restrict_nonpos_seq] at hx₂ 
      exact (some_exists_one_div_lt_subset hx₂).2 (Set.mem_Union.2 ⟨n, Set.mem_Union.2 ⟨nat.lt_succ_iff.mp h, hx₁⟩⟩)

private theorem restrict_nonpos_seq_disjoint : Pairwise (Disjoint on restrict_nonpos_seq s i) :=
  by 
    intro n m h 
    rcases lt_or_gt_of_neₓ h with (h | h)
    ·
      intro x 
      rw [Set.inf_eq_inter, restrict_nonpos_seq_disjoint' h]
      exact id
    ·
      intro x 
      rw [Set.inf_eq_inter, Set.inter_comm, restrict_nonpos_seq_disjoint' h]
      exact id

-- error in MeasureTheory.Decomposition.SignedHahn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem exists_subset_restrict_nonpos'
(hi₁ : measurable_set i)
(hi₂ : «expr < »(s i, 0))
(hn : «expr¬ »(∀
  n : exprℕ(), «expr¬ »(«expr ≤[ ] »(s, «expr \ »(i, «expr⋃ , »((l «expr < » n), restrict_nonpos_seq s i l)), 0)))) : «expr∃ , »((j : set α), «expr ∧ »(measurable_set j, «expr ∧ »(«expr ⊆ »(j, i), «expr ∧ »(«expr ≤[ ] »(s, j, 0), «expr < »(s j, 0))))) :=
begin
  by_cases [expr «expr ≤[ ] »(s, i, 0)],
  { exact [expr ⟨i, hi₁, set.subset.refl _, h, hi₂⟩] },
  push_neg ["at", ident hn],
  set [] [ident k] [] [":="] [expr nat.find hn] ["with", ident hk₁],
  have [ident hk₂] [":", expr «expr ≤[ ] »(s, «expr \ »(i, «expr⋃ , »((l «expr < » k), restrict_nonpos_seq s i l)), 0)] [":=", expr nat.find_spec hn],
  have [ident hmeas] [":", expr measurable_set «expr⋃ , »((l : exprℕ())
    (H : «expr < »(l, k)), restrict_nonpos_seq s i l)] [":=", expr «expr $ »(measurable_set.Union, λ
    _, measurable_set.Union_Prop (λ _, restrict_nonpos_seq_measurable_set _))],
  refine [expr ⟨«expr \ »(i, «expr⋃ , »((l «expr < » k), restrict_nonpos_seq s i l)), hi₁.diff hmeas, set.diff_subset _ _, hk₂, _⟩],
  rw ["[", expr of_diff hmeas hi₁, ",", expr s.of_disjoint_Union_nat, "]"] [],
  { have [ident h₁] [":", expr ∀ l «expr < » k, «expr ≤ »(0, s (restrict_nonpos_seq s i l))] [],
    { intros [ident l, ident hl],
      refine [expr le_of_lt (measure_of_restrict_nonpos_seq h _ _)],
      refine [expr mt (restrict_le_zero_subset _ (hi₁.diff _) (set.subset.refl _)) (nat.find_min hn hl)],
      exact [expr «expr $ »(measurable_set.Union, λ
        _, measurable_set.Union_Prop (λ _, restrict_nonpos_seq_measurable_set _))] },
    suffices [] [":", expr «expr ≤ »(0, «expr∑' , »((l : exprℕ()), s «expr⋃ , »((H : «expr < »(l, k)), restrict_nonpos_seq s i l)))],
    { rw [expr sub_neg] [],
      exact [expr lt_of_lt_of_le hi₂ this] },
    refine [expr tsum_nonneg _],
    intro [ident l],
    by_cases [expr «expr < »(l, k)],
    { convert [] [expr h₁ _ h] [],
      ext [] [ident x] [],
      rw ["[", expr set.mem_Union, ",", expr exists_prop, ",", expr and_iff_right_iff_imp, "]"] [],
      exact [expr λ _, h] },
    { convert [] [expr le_of_eq s.empty.symm] [],
      ext [] [] [],
      simp [] [] ["only"] ["[", expr exists_prop, ",", expr set.mem_empty_eq, ",", expr set.mem_Union, ",", expr not_and, ",", expr iff_false, "]"] [] [],
      exact [expr λ h', false.elim (h h')] } },
  { intro [],
    exact [expr measurable_set.Union_Prop (λ _, restrict_nonpos_seq_measurable_set _)] },
  { intros [ident a, ident b, ident hab, ident x, ident hx],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr set.mem_Union, ",", expr set.mem_inter_eq, ",", expr set.inf_eq_inter, "]"] [] ["at", ident hx],
    exact [expr let ⟨⟨_, hx₁⟩, _, hx₂⟩ := hx in restrict_nonpos_seq_disjoint a b hab ⟨hx₁, hx₂⟩] },
  { apply [expr set.Union_subset],
    intros [ident a, ident x],
    simp [] [] ["only"] ["[", expr and_imp, ",", expr exists_prop, ",", expr set.mem_Union, "]"] [] [],
    intros ["_", ident hx],
    exact [expr restrict_nonpos_seq_subset _ hx] },
  { apply_instance }
end

-- error in MeasureTheory.Decomposition.SignedHahn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A measurable set of negative measure has a negative subset of negative measure. -/
theorem exists_subset_restrict_nonpos
(hi : «expr < »(s i, 0)) : «expr∃ , »((j : set α), «expr ∧ »(measurable_set j, «expr ∧ »(«expr ⊆ »(j, i), «expr ∧ »(«expr ≤[ ] »(s, j, 0), «expr < »(s j, 0))))) :=
begin
  have [ident hi₁] [":", expr measurable_set i] [":=", expr classical.by_contradiction (λ
    h, «expr $ »(ne_of_lt hi, s.not_measurable h))],
  by_cases [expr «expr ≤[ ] »(s, i, 0)],
  { exact [expr ⟨i, hi₁, set.subset.refl _, h, hi⟩] },
  by_cases [expr hn, ":", expr ∀
   n : exprℕ(), «expr¬ »(«expr ≤[ ] »(s, «expr \ »(i, «expr⋃ , »((l «expr < » n), restrict_nonpos_seq s i l)), 0))],
  swap,
  { exact [expr exists_subset_restrict_nonpos' hi₁ hi hn] },
  set [] [ident A] [] [":="] [expr «expr \ »(i, «expr⋃ , »((l), restrict_nonpos_seq s i l))] ["with", ident hA],
  set [] [ident bdd] [":", expr exprℕ() → exprℕ()] [":="] [expr λ
   n, find_exists_one_div_lt s «expr \ »(i, «expr⋃ , »((k «expr ≤ » n), restrict_nonpos_seq s i k))] ["with", ident hbdd],
  have [ident hn'] [":", expr ∀
   n : exprℕ(), «expr¬ »(«expr ≤[ ] »(s, «expr \ »(i, «expr⋃ , »((l «expr ≤ » n), restrict_nonpos_seq s i l)), 0))] [],
  { intro [ident n],
    convert [] [expr hn «expr + »(n, 1)] []; { ext [] [ident l] [],
      simp [] [] ["only"] ["[", expr exists_prop, ",", expr set.mem_Union, ",", expr and.congr_left_iff, "]"] [] [],
      exact [expr λ _, nat.lt_succ_iff.symm] } },
  have [ident h₁] [":", expr «expr = »(s i, «expr + »(s A, «expr∑' , »((l), s (restrict_nonpos_seq s i l))))] [],
  { rw ["[", expr hA, ",", "<-", expr s.of_disjoint_Union_nat, ",", expr add_comm, ",", expr of_add_of_diff, "]"] [],
    exact [expr measurable_set.Union (λ _, restrict_nonpos_seq_measurable_set _)],
    exacts ["[", expr hi₁, ",", expr set.Union_subset (λ
      _, restrict_nonpos_seq_subset _), ",", expr λ
     _, restrict_nonpos_seq_measurable_set _, ",", expr restrict_nonpos_seq_disjoint, "]"] },
  have [ident h₂] [":", expr «expr ≤ »(s A, s i)] [],
  { rw [expr h₁] [],
    apply [expr le_add_of_nonneg_right],
    exact [expr tsum_nonneg (λ n, le_of_lt (measure_of_restrict_nonpos_seq h _ (hn n)))] },
  have [ident h₃'] [":", expr summable (λ n, («expr / »(1, «expr + »(bdd n, 1)) : exprℝ()))] [],
  { have [] [":", expr summable (λ
      l, s (restrict_nonpos_seq s i l))] [":=", expr has_sum.summable (s.m_Union (λ
       _, restrict_nonpos_seq_measurable_set _) restrict_nonpos_seq_disjoint)],
    refine [expr summable_of_nonneg_of_le (λ n, _) (λ n, _) (summable.comp_injective this nat.succ_injective)],
    { exact [expr le_of_lt nat.one_div_pos_of_nat] },
    { exact [expr le_of_lt (restrict_nonpos_seq_lt n (hn' n))] } },
  have [ident h₃] [":", expr tendsto (λ n, «expr + »((bdd n : exprℝ()), 1)) at_top at_top] [],
  { simp [] [] ["only"] ["[", expr one_div, "]"] [] ["at", ident h₃'],
    exact [expr summable.tendsto_top_of_pos h₃' (λ n, nat.cast_add_one_pos (bdd n))] },
  have [ident h₄] [":", expr tendsto (λ n, (bdd n : exprℝ())) at_top at_top] [],
  { convert [] [expr at_top.tendsto_at_top_add_const_right «expr- »(1) h₃] [],
    simp [] [] [] [] [] [] },
  have [ident A_meas] [":", expr measurable_set A] [":=", expr hi₁.diff (measurable_set.Union (λ
     _, restrict_nonpos_seq_measurable_set _))],
  refine [expr ⟨A, A_meas, set.diff_subset _ _, _, h₂.trans_lt hi⟩],
  by_contra [ident hnn],
  rw [expr restrict_le_restrict_iff _ _ A_meas] ["at", ident hnn],
  push_neg ["at", ident hnn],
  obtain ["⟨", ident E, ",", ident hE₁, ",", ident hE₂, ",", ident hE₃, "⟩", ":=", expr hnn],
  have [] [":", expr «expr∃ , »((k), «expr ∧ »(«expr ≤ »(1, bdd k), «expr < »(«expr / »(1, (bdd k : exprℝ())), s E)))] [],
  { rw [expr tendsto_at_top_at_top] ["at", ident h₄],
    obtain ["⟨", ident k, ",", ident hk, "⟩", ":=", expr h₄ (max «expr + »(«expr / »(1, s E), 1) 1)],
    refine [expr ⟨k, _, _⟩],
    { have [ident hle] [] [":=", expr le_of_max_le_right (hk k le_rfl)],
      norm_cast ["at", ident hle],
      exact [expr hle] },
    { have [] [":", expr «expr < »(«expr / »(1, s E), bdd k)] [],
      { linarith [] [] ["[", expr le_of_max_le_left (hk k le_rfl), "]"] { restrict_type := exprℝ() } },
      rw [expr one_div] ["at", ident this, "⊢"],
      rwa [expr inv_lt (lt_trans (inv_pos.2 hE₃) this) hE₃] [] } },
  obtain ["⟨", ident k, ",", ident hk₁, ",", ident hk₂, "⟩", ":=", expr this],
  have [ident hA'] [":", expr «expr ⊆ »(A, «expr \ »(i, «expr⋃ , »((l «expr ≤ » k), restrict_nonpos_seq s i l)))] [],
  { apply [expr set.diff_subset_diff_right],
    intro [ident x],
    simp [] [] ["only"] ["[", expr set.mem_Union, "]"] [] [],
    rintro ["⟨", ident n, ",", "_", ",", ident hn₂, "⟩"],
    exact [expr ⟨n, hn₂⟩] },
  refine [expr find_exists_one_div_lt_min (hn' k) (buffer.lt_aux_2 hk₁) ⟨E, set.subset.trans hE₂ hA', hE₁, _⟩],
  convert [] [expr hk₂] [],
  norm_cast [],
  exact [expr tsub_add_cancel_of_le hk₁]
end

end ExistsSubsetRestrictNonpos

/-- The set of measures of the set of measurable negative sets. -/
def measure_of_negatives (s : signed_measure α) : Set ℝ :=
  s '' { B | MeasurableSet B ∧ s ≤[B] 0 }

theorem zero_mem_measure_of_negatives : (0 : ℝ) ∈ s.measure_of_negatives :=
  ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.empty⟩

-- error in MeasureTheory.Decomposition.SignedHahn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bdd_below_measure_of_negatives : bdd_below s.measure_of_negatives :=
begin
  simp_rw ["[", expr bdd_below, ",", expr set.nonempty, ",", expr mem_lower_bounds, "]"] [],
  by_contra [],
  push_neg ["at", ident h],
  have [ident h'] [":", expr ∀
   n : exprℕ(), «expr∃ , »((y : exprℝ()), «expr ∧ »(«expr ∈ »(y, s.measure_of_negatives), «expr < »(y, «expr- »(n))))] [":=", expr λ
   n, h «expr- »(n)],
  choose [] [ident f] [ident hf] ["using", expr h'],
  have [ident hf'] [":", expr ∀
   n : exprℕ(), «expr∃ , »((B), «expr ∧ »(measurable_set B, «expr ∧ »(«expr ≤[ ] »(s, B, 0), «expr < »(s B, «expr- »(n)))))] [],
  { intro [ident n],
    rcases [expr hf n, "with", "⟨", "⟨", ident B, ",", "⟨", ident hB₁, ",", ident hBr, "⟩", ",", ident hB₂, "⟩", ",", ident hlt, "⟩"],
    exact [expr ⟨B, hB₁, hBr, «expr ▸ »(hB₂.symm, hlt)⟩] },
  choose [] [ident B] [ident hmeas, ident hr, ident h_lt] ["using", expr hf'],
  set [] [ident A] [] [":="] [expr «expr⋃ , »((n), B n)] ["with", ident hA],
  have [ident hfalse] [":", expr ∀ n : exprℕ(), «expr ≤ »(s A, «expr- »(n))] [],
  { intro [ident n],
    refine [expr le_trans _ (le_of_lt (h_lt _))],
    rw ["[", expr hA, ",", "<-", expr set.diff_union_of_subset (set.subset_Union _ n), ",", expr of_union (disjoint.comm.1 set.disjoint_diff) _ (hmeas n), "]"] [],
    { refine [expr add_le_of_nonpos_left _],
      have [] [":", expr «expr ≤[ ] »(s, A, 0)] [":=", expr restrict_le_restrict_Union _ _ hmeas hr],
      refine [expr nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ _ (set.diff_subset _ _) this)],
      exact [expr measurable_set.Union hmeas] },
    { apply_instance },
    { exact [expr (measurable_set.Union hmeas).diff (hmeas n)] } },
  rcases [expr exists_nat_gt «expr- »(s A), "with", "⟨", ident n, ",", ident hn, "⟩"],
  exact [expr lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))]
end

-- error in MeasureTheory.Decomposition.SignedHahn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Alternative formulation of `measure_theory.signed_measure.exists_is_compl_positive_negative`
(the Hahn decomposition theorem) using set complements. -/
theorem exists_compl_positive_negative
(s : signed_measure α) : «expr∃ , »((i : set α), «expr ∧ »(measurable_set i, «expr ∧ »(«expr ≤[ ] »(0, i, s), «expr ≤[ ] »(s, «expr ᶜ»(i), 0)))) :=
begin
  obtain ["⟨", ident f, ",", "_", ",", ident hf₂, ",", ident hf₁, "⟩", ":=", expr exists_seq_tendsto_Inf ⟨0, @zero_mem_measure_of_negatives _ _ s⟩ bdd_below_measure_of_negatives],
  choose [] [ident B] [ident hB] ["using", expr hf₁],
  have [ident hB₁] [":", expr ∀ n, measurable_set (B n)] [":=", expr λ n, (hB n).1.1],
  have [ident hB₂] [":", expr ∀ n, «expr ≤[ ] »(s, B n, 0)] [":=", expr λ n, (hB n).1.2],
  set [] [ident A] [] [":="] [expr «expr⋃ , »((n), B n)] ["with", ident hA],
  have [ident hA₁] [":", expr measurable_set A] [":=", expr measurable_set.Union hB₁],
  have [ident hA₂] [":", expr «expr ≤[ ] »(s, A, 0)] [":=", expr restrict_le_restrict_Union _ _ hB₁ hB₂],
  have [ident hA₃] [":", expr «expr = »(s A, Inf s.measure_of_negatives)] [],
  { apply [expr le_antisymm],
    { refine [expr le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (eventually_of_forall (λ n, _))],
      rw ["[", "<-", expr (hB n).2, ",", expr hA, ",", "<-", expr set.diff_union_of_subset (set.subset_Union _ n), ",", expr of_union (disjoint.comm.1 set.disjoint_diff) _ (hB₁ n), "]"] [],
      { refine [expr add_le_of_nonpos_left _],
        have [] [":", expr «expr ≤[ ] »(s, A, 0)] [":=", expr restrict_le_restrict_Union _ _ hB₁ (λ
          m, let ⟨_, h⟩ := (hB m).1 in
          h)],
        refine [expr nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ _ (set.diff_subset _ _) this)],
        exact [expr measurable_set.Union hB₁] },
      { apply_instance },
      { exact [expr (measurable_set.Union hB₁).diff (hB₁ n)] } },
    { exact [expr cInf_le bdd_below_measure_of_negatives ⟨A, ⟨hA₁, hA₂⟩, rfl⟩] } },
  refine [expr ⟨«expr ᶜ»(A), hA₁.compl, _, «expr ▸ »((compl_compl A).symm, hA₂)⟩],
  rw [expr restrict_le_restrict_iff _ _ hA₁.compl] [],
  intros [ident C, ident hC, ident hC₁],
  by_contra [ident hC₂],
  push_neg ["at", ident hC₂],
  rcases [expr exists_subset_restrict_nonpos hC₂, "with", "⟨", ident D, ",", ident hD₁, ",", ident hD, ",", ident hD₂, ",", ident hD₃, "⟩"],
  have [] [":", expr «expr < »(s «expr ∪ »(A, D), Inf s.measure_of_negatives)] [],
  { rw ["[", "<-", expr hA₃, ",", expr of_union (set.disjoint_of_subset_right (set.subset.trans hD hC₁) disjoint_compl_right) hA₁ hD₁, "]"] [],
    linarith [] [] [],
    apply_instance },
  refine [expr not_le.2 this _],
  refine [expr cInf_le bdd_below_measure_of_negatives ⟨«expr ∪ »(A, D), ⟨_, _⟩, rfl⟩],
  { exact [expr hA₁.union hD₁] },
  { exact [expr restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂] }
end

/-- **The Hahn decomposition thoerem**: Given a signed measure `s`, there exist
complement measurable sets `i` and `j` such that `i` is positive, `j` is negative. -/
theorem exists_is_compl_positive_negative (s : signed_measure α) :
  ∃ i j : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ MeasurableSet j ∧ s ≤[j] 0 ∧ IsCompl i j :=
  let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, «expr ᶜ» i, hi₁, hi₂, hi₁.compl, hi₃, is_compl_compl⟩

/-- The symmetric difference of two Hahn decompositions have measure zero. -/
theorem of_symm_diff_compl_positive_negative {s : signed_measure α} {i j : Set α} (hi : MeasurableSet i)
  (hj : MeasurableSet j) (hi' : 0 ≤[i] s ∧ s ≤[«expr ᶜ» i] 0) (hj' : 0 ≤[j] s ∧ s ≤[«expr ᶜ» j] 0) :
  s (i Δ j) = 0 ∧ s («expr ᶜ» i Δ «expr ᶜ» j) = 0 :=
  by 
    rw [restrict_le_restrict_iff s 0, restrict_le_restrict_iff 0 s] at hi' hj' 
    split 
    ·
      rw [symm_diff_def, Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, Set.sup_eq_union, of_union,
        le_antisymmₓ (hi'.2 (hi.compl.inter hj) (Set.inter_subset_left _ _))
          (hj'.1 (hi.compl.inter hj) (Set.inter_subset_right _ _)),
        le_antisymmₓ (hj'.2 (hj.compl.inter hi) (Set.inter_subset_left _ _))
          (hi'.1 (hj.compl.inter hi) (Set.inter_subset_right _ _)),
        zero_apply, zero_apply, zero_addₓ]
      ·
        exact
          Set.disjoint_of_subset_left (Set.inter_subset_left _ _)
            (Set.disjoint_of_subset_right (Set.inter_subset_right _ _)
              (Disjoint.comm.1 (IsCompl.disjoint is_compl_compl)))
      ·
        exact hj.compl.inter hi
      ·
        exact hi.compl.inter hj
    ·
      rw [symm_diff_def, Set.diff_eq_compl_inter, Set.diff_eq_compl_inter, compl_compl, compl_compl, Set.sup_eq_union,
        of_union,
        le_antisymmₓ (hi'.2 (hj.inter hi.compl) (Set.inter_subset_right _ _))
          (hj'.1 (hj.inter hi.compl) (Set.inter_subset_left _ _)),
        le_antisymmₓ (hj'.2 (hi.inter hj.compl) (Set.inter_subset_right _ _))
          (hi'.1 (hi.inter hj.compl) (Set.inter_subset_left _ _)),
        zero_apply, zero_apply, zero_addₓ]
      ·
        exact
          Set.disjoint_of_subset_left (Set.inter_subset_left _ _)
            (Set.disjoint_of_subset_right (Set.inter_subset_right _ _) (IsCompl.disjoint is_compl_compl))
      ·
        exact hj.inter hi.compl
      ·
        exact hi.inter hj.compl 
    all_goals 
      measurability

end SignedMeasure

end MeasureTheory

