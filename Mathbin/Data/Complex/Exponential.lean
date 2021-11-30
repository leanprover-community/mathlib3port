import Mathbin.Algebra.GeomSum 
import Mathbin.Data.Complex.Basic 
import Mathbin.Data.Nat.Choose.Sum

/-!
# Exponential, trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the real and complex exponential, sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/


local notation "abs'" => HasAbs.abs

open IsAbsoluteValue

open_locale Classical BigOperators Nat ComplexConjugate

section 

open Real IsAbsoluteValue Finset

section 

variable {α : Type _} {β : Type _} [Ringₓ β] [LinearOrderedField α] [Archimedean α] {abv : β → α} [IsAbsoluteValue abv]

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_cau_of_decreasing_bounded
(f : exprℕ() → α)
{a : α}
{m : exprℕ()}
(ham : ∀ n «expr ≥ » m, «expr ≤ »(«expr| |»(f n), a))
(hnm : ∀ n «expr ≥ » m, «expr ≤ »(f n.succ, f n)) : is_cau_seq abs f :=
λ ε ε0, let ⟨k, hk⟩ := archimedean.arch a ε0 in
have h : «expr∃ , »((l), ∀
 n «expr ≥ » m, «expr < »(«expr - »(a, «expr • »(l, ε)), f n)) := ⟨«expr + »(«expr + »(k, k), 1), λ
 n
 hnm, lt_of_lt_of_le (show «expr < »(«expr - »(a, «expr • »(«expr + »(k, «expr + »(k, 1)), ε)), «expr- »(«expr| |»(f n))), from «expr $ »(lt_neg.1, lt_of_le_of_lt (ham n hnm) (begin
      rw ["[", expr neg_sub, ",", expr lt_sub_iff_add_lt, ",", expr add_nsmul, ",", expr add_nsmul, ",", expr one_nsmul, "]"] [],
      exact [expr add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk (lt_add_of_pos_right _ ε0))]
    end))) «expr $ »(neg_le.2, «expr ▸ »(abs_neg (f n), le_abs_self _))⟩,
let l := nat.find h in
have hl : ∀ n : exprℕ(), «expr ≥ »(n, m) → «expr > »(f n, «expr - »(a, «expr • »(l, ε))) := nat.find_spec h,
have hl0 : «expr ≠ »(l, 0) := λ
hl0, not_lt_of_ge (ham m (le_refl _)) (lt_of_lt_of_le (by have [] [] [":=", expr hl m (le_refl m)]; simpa [] [] [] ["[", expr hl0, "]"] [] ["using", expr this]) (le_abs_self (f m))),
begin
  cases [expr not_forall.1 (nat.find_min h (nat.pred_lt hl0))] ["with", ident i, ident hi],
  rw ["[", expr not_imp, ",", expr not_lt, "]"] ["at", ident hi],
  existsi [expr i],
  assume [binders (j hj)],
  have [ident hfij] [":", expr «expr ≤ »(f j, f i)] [":=", expr forall_ge_le_of_forall_le_succ f hnm hi.1 hj],
  rw ["[", expr abs_of_nonpos (sub_nonpos.2 hfij), ",", expr neg_sub, ",", expr sub_lt_iff_lt_add', "]"] [],
  calc
    «expr ≤ »(f i, «expr - »(a, «expr • »(nat.pred l, ε))) : hi.2
    «expr = »(..., «expr + »(«expr - »(a, «expr • »(l, ε)), ε)) : by conv [] [] { to_rhs,
      rw ["[", "<-", expr nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hl0), ",", expr succ_nsmul', ",", expr sub_add, ",", expr add_sub_cancel, "]"] }
    «expr < »(..., «expr + »(f j, ε)) : add_lt_add_right (hl j (le_trans hi.1 hj)) _
end

theorem is_cau_of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n _ : n ≥ m, |f n| ≤ a)
  (hnm : ∀ n _ : n ≥ m, f n ≤ f n.succ) : IsCauSeq abs f :=
  by 
    refine'
      @Eq.recOnₓ (ℕ → α) _ (IsCauSeq abs) _ _
        (-⟨_,
              @is_cau_of_decreasing_bounded _ _ _ (fun n => -f n) a m
                (by 
                  simpa)
                (by 
                  simpa)⟩ :
          CauSeq α abs).2
          
    ext 
    exact neg_negₓ _

end 

section NoArchimedean

variable {α : Type _} {β : Type _} [Ringₓ β] [LinearOrderedField α] {abv : β → α} [IsAbsoluteValue abv]

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_cau_series_of_abv_le_cau
{f : exprℕ() → β}
{g : exprℕ() → α}
(n : exprℕ()) : ∀
m, «expr ≤ »(n, m) → «expr ≤ »(abv (f m), g m) → is_cau_seq abs (λ
 n, «expr∑ in , »((i), range n, g i)) → is_cau_seq abv (λ n, «expr∑ in , »((i), range n, f i)) :=
begin
  assume [binders (hm hg ε ε0)],
  cases [expr hg «expr / »(ε, 2) (div_pos ε0 (by norm_num [] []))] ["with", ident i, ident hi],
  existsi [expr max n i],
  assume [binders (j ji)],
  have [ident hi₁] [] [":=", expr hi j (le_trans (le_max_right n i) ji)],
  have [ident hi₂] [] [":=", expr hi (max n i) (le_max_right n i)],
  have [ident sub_le] [] [":=", expr abs_sub_le «expr∑ in , »((k), range j, g k) «expr∑ in , »((k), range i, g k) «expr∑ in , »((k), range (max n i), g k)],
  have [] [] [":=", expr add_lt_add hi₁ hi₂],
  rw ["[", expr abs_sub_comm «expr∑ in , »((k), range (max n i), g k), ",", expr add_halves ε, "]"] ["at", ident this],
  refine [expr lt_of_le_of_lt (le_trans (le_trans _ (le_abs_self _)) sub_le) this],
  generalize [ident hk] [":"] [expr «expr = »(«expr - »(j, max n i), k)],
  clear [ident this, ident hi₂, ident hi₁, ident hi, ident ε0, ident ε, ident hg, ident sub_le],
  rw [expr tsub_eq_iff_eq_add_of_le ji] ["at", ident hk],
  rw [expr hk] [],
  clear [ident hk, ident ji, ident j],
  induction [expr k] [] ["with", ident k', ident hi] [],
  { simp [] [] [] ["[", expr abv_zero abv, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr nat.succ_add, ",", expr sum_range_succ_comm, ",", expr sub_eq_add_neg, ",", expr add_assoc, "]"] [] [],
    refine [expr le_trans (abv_add _ _ _) _],
    simp [] [] ["only"] ["[", expr sub_eq_add_neg, "]"] [] ["at", ident hi],
    exact [expr add_le_add (hm _ (le_add_of_nonneg_of_le (nat.zero_le _) (le_max_left _ _))) hi] }
end

theorem is_cau_series_of_abv_cau {f : ℕ → β} :
  (IsCauSeq abs fun m => ∑n in range m, abv (f n)) → IsCauSeq abv fun m => ∑n in range m, f n :=
  is_cau_series_of_abv_le_cau 0 fun n h => le_reflₓ _

end NoArchimedean

section 

variable {α : Type _} {β : Type _} [Ringₓ β] [LinearOrderedField α] [Archimedean α] {abv : β → α} [IsAbsoluteValue abv]

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_cau_geo_series
{β : Type*}
[field β]
{abv : β → α}
[is_absolute_value abv]
(x : β)
(hx1 : «expr < »(abv x, 1)) : is_cau_seq abv (λ n, «expr∑ in , »((m), range n, «expr ^ »(x, m))) :=
have hx1' : «expr ≠ »(abv x, 1) := λ
h, by simpa [] [] [] ["[", expr h, ",", expr lt_irrefl, "]"] [] ["using", expr hx1],
is_cau_series_of_abv_cau (begin
   simp [] [] ["only"] ["[", expr abv_pow abv, "]"] [] [] { eta := ff },
   have [] [":", expr «expr = »(λ
     m : exprℕ(), «expr∑ in , »((n), range m, «expr ^ »(abv x, n)), λ m, geom_sum (abv x) m)] [":=", expr rfl],
   simp [] [] ["only"] ["[", expr this, ",", expr geom_sum_eq hx1', "]"] [] [] { eta := ff },
   conv [] ["in", expr «expr / »(_, _)] { rw ["[", "<-", expr neg_div_neg_eq, ",", expr neg_sub, ",", expr neg_sub, "]"] },
   refine [expr @is_cau_of_mono_bounded _ _ _ _ «expr / »((1 : α), «expr - »(1, abv x)) 0 _ _],
   { assume [binders (n hn)],
     rw [expr abs_of_nonneg] [],
     refine [expr div_le_div_of_le «expr $ »(le_of_lt, sub_pos.2 hx1) (sub_le_self _ «expr ▸ »(abv_pow abv x n, abv_nonneg _ _))],
     refine [expr div_nonneg (sub_nonneg.2 _) «expr $ »(sub_nonneg.2, le_of_lt hx1)],
     clear [ident hn],
     induction [expr n] [] ["with", ident n, ident ih] [],
     { simp [] [] [] [] [] [] },
     { rw ["[", expr pow_succ, ",", "<-", expr one_mul (1 : α), "]"] [],
       refine [expr mul_le_mul (le_of_lt hx1) ih «expr ▸ »(abv_pow abv x n, abv_nonneg _ _) (by norm_num [] [])] } },
   { assume [binders (n hn)],
     refine [expr div_le_div_of_le «expr $ »(le_of_lt, sub_pos.2 hx1) (sub_le_sub_left _ _)],
     rw ["[", "<-", expr one_mul «expr ^ »(_, n), ",", expr pow_succ, "]"] [],
     exact [expr mul_le_mul_of_nonneg_right (le_of_lt hx1) (pow_nonneg (abv_nonneg _ _) _)] }
 end)

theorem is_cau_geo_series_const (a : α) {x : α} (hx1 : |x| < 1) : IsCauSeq abs fun m => ∑n in range m, a*x ^ n :=
  have  : IsCauSeq abs fun m => a*∑n in range m, x ^ n := (CauSeq.const abs a*⟨_, is_cau_geo_series x hx1⟩).2
  by 
    simpa only [mul_sum]

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem series_ratio_test
{f : exprℕ() → β}
(n : exprℕ())
(r : α)
(hr0 : «expr ≤ »(0, r))
(hr1 : «expr < »(r, 1))
(h : ∀
 m, «expr ≤ »(n, m) → «expr ≤ »(abv (f m.succ), «expr * »(r, abv (f m)))) : is_cau_seq abv (λ
 m, «expr∑ in , »((n), range m, f n)) :=
have har1 : «expr < »(«expr| |»(r), 1), by rwa [expr abs_of_nonneg hr0] [],
begin
  refine [expr is_cau_series_of_abv_le_cau n.succ _ (is_cau_geo_series_const «expr * »(abv (f n.succ), «expr ^ »(«expr ⁻¹»(r), n.succ)) har1)],
  assume [binders (m hmn)],
  cases [expr classical.em «expr = »(r, 0)] ["with", ident r_zero, ident r_ne_zero],
  { have [ident m_pos] [] [":=", expr lt_of_lt_of_le (nat.succ_pos n) hmn],
    have [] [] [":=", expr h m.pred (nat.le_of_succ_le_succ (by rwa ["[", expr nat.succ_pred_eq_of_pos m_pos, "]"] []))],
    simpa [] [] [] ["[", expr r_zero, ",", expr nat.succ_pred_eq_of_pos m_pos, ",", expr pow_succ, "]"] [] [] },
  generalize [ident hk] [":"] [expr «expr = »(«expr - »(m, n.succ), k)],
  have [ident r_pos] [":", expr «expr < »(0, r)] [":=", expr lt_of_le_of_ne hr0 (ne.symm r_ne_zero)],
  replace [ident hk] [":", expr «expr = »(m, «expr + »(k, n.succ))] [":=", expr (tsub_eq_iff_eq_add_of_le hmn).1 hk],
  induction [expr k] [] ["with", ident k, ident ih] ["generalizing", ident m, ident n],
  { rw ["[", expr hk, ",", expr zero_add, ",", expr mul_right_comm, ",", expr inv_pow₀ _ _, ",", "<-", expr div_eq_mul_inv, ",", expr mul_div_cancel, "]"] [],
    exact [expr (ne_of_lt (pow_pos r_pos _)).symm] },
  { have [ident kn] [":", expr «expr ≥ »(«expr + »(k, n.succ), n.succ)] [],
    by rw ["<-", expr zero_add n.succ] []; exact [expr add_le_add (zero_le _) (by simp [] [] [] [] [] [])],
    rw ["[", expr hk, ",", expr nat.succ_add, ",", expr pow_succ' r, ",", "<-", expr mul_assoc, "]"] [],
    exact [expr le_trans (by rw [expr mul_comm] []; exact [expr h _ (nat.le_of_succ_le kn)]) (mul_le_mul_of_nonneg_right (ih «expr + »(k, n.succ) n h kn rfl) hr0)] }
end

theorem sum_range_diag_flip {α : Type _} [AddCommMonoidₓ α] (n : ℕ) (f : ℕ → ℕ → α) :
  (∑m in range n, ∑k in range (m+1), f k (m - k)) = ∑m in range n, ∑k in range (n - m), f m k :=
  by 
    rw [sum_sigma', sum_sigma'] <;>
      exact
        sum_bij (fun a _ => ⟨a.2, a.1 - a.2⟩)
          (fun a ha =>
            have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1
            have h₂ : a.2 < Nat.succ a.1 := mem_range.1 (mem_sigma.1 ha).2
            mem_sigma.2
              ⟨mem_range.2 (lt_of_lt_of_leₓ h₂ h₁),
                mem_range.2 ((tsub_lt_tsub_iff_right (Nat.le_of_lt_succₓ h₂)).2 h₁)⟩)
          (fun _ _ => rfl)
          (fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h =>
            have ha : a₁ < n ∧ a₂ ≤ a₁ :=
              ⟨mem_range.1 (mem_sigma.1 ha).1, Nat.le_of_lt_succₓ (mem_range.1 (mem_sigma.1 ha).2)⟩
            have hb : b₁ < n ∧ b₂ ≤ b₁ :=
              ⟨mem_range.1 (mem_sigma.1 hb).1, Nat.le_of_lt_succₓ (mem_range.1 (mem_sigma.1 hb).2)⟩
            have h : a₂ = b₂ ∧ _ := Sigma.mk.inj h 
            have h' : a₁ = (b₁ - b₂)+a₂ := (tsub_eq_iff_eq_add_of_le ha.2).1 (eq_of_heq h.2)
            Sigma.mk.inj_iff.2 ⟨tsub_add_cancel_of_le hb.2 ▸ h'.symm ▸ h.1 ▸ rfl, heq_of_eq h.1⟩)
          fun ⟨a₁, a₂⟩ ha =>
            have ha : a₁ < n ∧ a₂ < n - a₁ := ⟨mem_range.1 (mem_sigma.1 ha).1, mem_range.1 (mem_sigma.1 ha).2⟩
            ⟨⟨a₂+a₁, a₁⟩,
              ⟨mem_sigma.2
                  ⟨mem_range.2 (lt_tsub_iff_right.1 ha.2), mem_range.2 (Nat.lt_succ_of_leₓ (Nat.le_add_leftₓ _ _))⟩,
                Sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq (add_tsub_cancel_right _ _).symm⟩⟩⟩

theorem sum_range_sub_sum_range {α : Type _} [AddCommGroupₓ α] {f : ℕ → α} {n m : ℕ} (hnm : n ≤ m) :
  ((∑k in range m, f k) - ∑k in range n, f k) = ∑k in (range m).filter fun k => n ≤ k, f k :=
  by 
    rw [←sum_sdiff (@filter_subset _ (fun k => n ≤ k) _ (range m)), sub_eq_iff_eq_add, ←eq_sub_iff_add_eq,
      add_sub_cancel']
    refine'
      Finset.sum_congr
        (Finset.ext$
          fun a =>
            ⟨fun h =>
                by 
                  simp  at * <;> finish,
              fun h =>
                have ham : a < m := lt_of_lt_of_leₓ (mem_range.1 h) hnm 
                by 
                  simp_all ⟩)
        fun _ _ => rfl

end 

section NoArchimedean

variable {α : Type _} {β : Type _} [Ringₓ β] [LinearOrderedField α] {abv : β → α} [IsAbsoluteValue abv]

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem abv_sum_le_sum_abv
{γ : Type*}
(f : γ → β)
(s : finset γ) : «expr ≤ »(abv «expr∑ in , »((k), s, f k), «expr∑ in , »((k), s, abv (f k))) :=
by haveI [] [] [":=", expr classical.dec_eq γ]; exact [expr finset.induction_on s (by simp [] [] [] ["[", expr abv_zero abv, "]"] [] []) (λ
  a
  s
  has
  ih, by rw ["[", expr sum_insert has, ",", expr sum_insert has, "]"] []; exact [expr le_trans (abv_add abv _ _) (add_le_add_left ih _)])]

theorem cauchy_product {a b : ℕ → β} (ha : IsCauSeq abs fun m => ∑n in range m, abv (a n))
  (hb : IsCauSeq abv fun m => ∑n in range m, b n) (ε : α) (ε0 : 0 < ε) :
  ∃ i : ℕ,
    ∀ j _ : j ≥ i,
      abv (((∑k in range j, a k)*∑k in range j, b k) - ∑n in range j, ∑m in range (n+1), a m*b (n - m)) < ε :=
  let ⟨Q, hQ⟩ := CauSeq.bounded ⟨_, hb⟩
  let ⟨P, hP⟩ := CauSeq.bounded ⟨_, ha⟩
  have hP0 : 0 < P := lt_of_le_of_ltₓ (abs_nonneg _) (hP 0)
  have hPε0 : 0 < ε / 2*P :=
    div_pos ε0
      (mul_pos
        (show (2 : α) > 0 from
          by 
            normNum)
        hP0)
  let ⟨N, hN⟩ := CauSeq.cauchy₂ ⟨_, hb⟩ hPε0 
  have hQε0 : 0 < ε / 4*Q :=
    div_pos ε0
      (mul_pos
        (show (0 : α) < 4by 
          normNum)
        (lt_of_le_of_ltₓ (abv_nonneg _ _) (hQ 0)))
  let ⟨M, hM⟩ := CauSeq.cauchy₂ ⟨_, ha⟩ hQε0
  ⟨2*max N M+1,
    fun K hK =>
      have h₁ : (∑m in range K, ∑k in range (m+1), a k*b (m - k)) = ∑m in range K, ∑n in range (K - m), a m*b n :=
        by 
          simpa using sum_range_diag_flip K fun m n => a m*b n 
      have h₂ : (fun i => ∑k in range (K - i), a i*b k) = fun i => a i*∑k in range (K - i), b k :=
        by 
          simp [Finset.mul_sum]
      have h₃ :
        (∑i in range K, a i*∑k in range (K - i), b k) =
          (∑i in range K, a i*(∑k in range (K - i), b k) - ∑k in range K, b k)+∑i in range K, a i*∑k in range K, b k :=
        by 
          rw [←sum_add_distrib] <;> simp [(mul_addₓ _ _ _).symm]
      have two_mul_two : (4 : α) = 2*2 :=
        by 
          normNum 
      have hQ0 : Q ≠ 0 :=
        fun h =>
          by 
            simpa [h, lt_irreflₓ] using hQε0 
      have h2Q0 : (2*Q) ≠ 0 := mul_ne_zero two_ne_zero hQ0 
      have hε : (((ε / 2*P)*P)+(ε / 4*Q)*2*Q) = ε :=
        by 
          rw [←div_div_eq_div_mul, div_mul_cancel _ (Ne.symm (ne_of_ltₓ hP0)), two_mul_two, mul_assocₓ,
            ←div_div_eq_div_mul, div_mul_cancel _ h2Q0, add_halves]
      have hNMK : (max N M+1) < K :=
        lt_of_lt_of_leₓ
          (by 
            rw [two_mul] <;> exact lt_add_of_pos_left _ (Nat.succ_posₓ _))
          hK 
      have hKN : N < K :=
        calc N ≤ max N M := le_max_leftₓ _ _ 
          _ < max N M+1 := Nat.lt_succ_selfₓ _ 
          _ < K := hNMK 
          
      have hsumlesum :
        (∑i in range (max N M+1), abv (a i)*abv ((∑k in range (K - i), b k) - ∑k in range K, b k)) ≤
          ∑i in range (max N M+1), abv (a i)*ε / 2*P :=
        sum_le_sum
          fun m hmJ =>
            mul_le_mul_of_nonneg_left
              (le_of_ltₓ
                (hN (K - m) K
                  (le_tsub_of_add_le_left
                    (le_transₓ
                      (by 
                        rw [two_mul] <;>
                          exact
                            add_le_add (le_of_ltₓ (mem_range.1 hmJ))
                              (le_transₓ (le_max_leftₓ _ _) (le_of_ltₓ (lt_add_one _))))
                      hK))
                  (le_of_ltₓ hKN)))
              (abv_nonneg abv _)
      have hsumltP : (∑n in range (max N M+1), abv (a n)) < P :=
        calc (∑n in range (max N M+1), abv (a n)) = |∑n in range (max N M+1), abv (a n)| :=
          Eq.symm (abs_of_nonneg (sum_nonneg fun x h => abv_nonneg abv (a x)))
          _ < P := hP (max N M+1)
          
      by 
        rw [h₁, h₂, h₃, sum_mul, ←sub_sub, sub_right_comm, sub_self, zero_sub, abv_neg abv]
        refine' lt_of_le_of_ltₓ (abv_sum_le_sum_abv _ _) _ 
        suffices  :
          ((∑i in range (max N M+1),
                abv
                    (a
                      i)*abv
                    ((∑k in range (K - i), b k) -
                      ∑k in range K,
                        b
                          k))+(∑i in range K, abv (a i)*abv ((∑k in range (K - i), b k) - ∑k in range K, b k)) -
                ∑i in range (max N M+1), abv (a i)*abv ((∑k in range (K - i), b k) - ∑k in range K, b k)) <
            ((ε / 2*P)*P)+(ε / 4*Q)*2*Q
        ·
          rw [hε] at this 
          simpa [abv_mul abv]
        refine'
          add_lt_add
            (lt_of_le_of_ltₓ hsumlesum
              (by 
                rw [←sum_mul, mul_commₓ] <;> exact (mul_lt_mul_left hPε0).mpr hsumltP))
            _ 
        rw [sum_range_sub_sum_range (le_of_ltₓ hNMK)]
        calc
          (∑i in (range K).filter fun k => (max N M+1) ≤ k,
              abv (a i)*abv ((∑k in range (K - i), b k) - ∑k in range K, b k)) ≤
            ∑i in (range K).filter fun k => (max N M+1) ≤ k, abv (a i)*2*Q :=
          sum_le_sum
            fun n hn =>
              by 
                refine' mul_le_mul_of_nonneg_left _ (abv_nonneg _ _)
                rw [sub_eq_add_neg]
                refine' le_transₓ (abv_add _ _ _) _ 
                rw [two_mul, abv_neg abv]
                exact add_le_add (le_of_ltₓ (hQ _)) (le_of_ltₓ (hQ _))_ < (ε / 4*Q)*2*Q :=
          by 
            rw [←sum_mul, ←sum_range_sub_sum_range (le_of_ltₓ hNMK)] <;>
              refine'
                (mul_lt_mul_right$
                      by 
                        rw [two_mul] <;>
                          exact
                            add_pos (lt_of_le_of_ltₓ (abv_nonneg _ _) (hQ 0))
                              (lt_of_le_of_ltₓ (abv_nonneg _ _) (hQ 0))).2
                  (lt_of_le_of_ltₓ (le_abs_self _)
                    (hM _ _ (le_transₓ (Nat.le_succ_of_leₓ (le_max_rightₓ _ _)) (le_of_ltₓ hNMK))
                      (Nat.le_succ_of_leₓ (le_max_rightₓ _ _))))⟩

end NoArchimedean

end 

open Finset

open CauSeq

namespace Complex

theorem is_cau_abs_exp (z : ℂ) : IsCauSeq HasAbs.abs fun n => ∑m in range n, abs (z ^ m / m !) :=
  let ⟨n, hn⟩ := exists_nat_gt (abs z)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_ltₓ (abs_nonneg _) hn 
  series_ratio_test n (Complex.abs z / n) (div_nonneg (Complex.abs_nonneg _) (le_of_ltₓ hn0))
    (by 
      rwa [div_lt_iff hn0, one_mulₓ])
    fun m hm =>
      by 
        rw [abs_abs, abs_abs, Nat.factorial_succ, pow_succₓ, mul_commₓ m.succ, Nat.cast_mul, ←div_div_eq_div_mul,
            mul_div_assoc, mul_div_right_comm, abs_mul, abs_div, abs_cast_nat] <;>
          exact
            mul_le_mul_of_nonneg_right
              (div_le_div_of_le_left (abs_nonneg _) hn0 (Nat.cast_le.2 (le_transₓ hm (Nat.le_succₓ _)))) (abs_nonneg _)

noncomputable theory

theorem is_cau_exp (z : ℂ) : IsCauSeq abs fun n => ∑m in range n, z ^ m / m ! :=
  is_cau_series_of_abv_cau (is_cau_abs_exp z)

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
def exp' (z : ℂ) : CauSeq ℂ Complex.abs :=
  ⟨fun n => ∑m in range n, z ^ m / m !, is_cau_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
@[pp_nodot]
def exp (z : ℂ) : ℂ :=
  limₓ (exp' z)

/-- The complex sine function, defined via `exp` -/
@[pp_nodot]
def sin (z : ℂ) : ℂ :=
  ((exp ((-z)*I) - exp (z*I))*I) / 2

/-- The complex cosine function, defined via `exp` -/
@[pp_nodot]
def cos (z : ℂ) : ℂ :=
  (exp (z*I)+exp ((-z)*I)) / 2

/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot]
def tan (z : ℂ) : ℂ :=
  sin z / cos z

/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot]
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / 2

/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot]
def cosh (z : ℂ) : ℂ :=
  (exp z+exp (-z)) / 2

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot]
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z

end Complex

namespace Real

open Complex

/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot]
def exp (x : ℝ) : ℝ :=
  (exp x).re

/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
def sin (x : ℝ) : ℝ :=
  (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
def cos (x : ℝ) : ℝ :=
  (cos x).re

/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot]
def tan (x : ℝ) : ℝ :=
  (tan x).re

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot]
def sinh (x : ℝ) : ℝ :=
  (sinh x).re

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
@[pp_nodot]
def cosh (x : ℝ) : ℝ :=
  (cosh x).re

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot]
def tanh (x : ℝ) : ℝ :=
  (tanh x).re

end Real

namespace Complex

variable (x y : ℂ)

@[simp]
theorem exp_zero : exp 0 = 1 :=
  lim_eq_of_equiv_const$
    fun ε ε0 =>
      ⟨1,
        fun j hj =>
          by 
            convert ε0 
            cases j
            ·
              exact absurd hj (not_le_of_gtₓ zero_lt_one)
            ·
              dsimp [exp']
              induction' j with j ih
              ·
                dsimp [exp'] <;> simp 
              ·
                rw
                  [←ih
                    (by 
                      decide)]
                simp only [sum_range_succ, pow_succₓ]
                simp ⟩

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_add : «expr = »(exp «expr + »(x, y), «expr * »(exp x, exp y)) :=
show «expr = »(lim (⟨_, is_cau_exp «expr + »(x, y)⟩ : cau_seq exprℂ() abs), «expr * »(lim (show cau_seq exprℂ() abs, from ⟨_, is_cau_exp x⟩), lim (show cau_seq exprℂ() abs, from ⟨_, is_cau_exp y⟩))), from have hj : ∀
j : exprℕ(), «expr = »(«expr∑ in , »((m), range j, «expr / »(«expr ^ »(«expr + »(x, y), m), «expr !»(m))), «expr∑ in , »((i), range j, «expr∑ in , »((k), range «expr + »(i, 1), «expr * »(«expr / »(«expr ^ »(x, k), «expr !»(k)), «expr / »(«expr ^ »(y, «expr - »(i, k)), «expr !»(«expr - »(i, k))))))), from assume
j, finset.sum_congr rfl (λ m hm, begin
   rw ["[", expr add_pow, ",", expr div_eq_mul_inv, ",", expr sum_mul, "]"] [],
   refine [expr finset.sum_congr rfl (λ i hi, _)],
   have [ident h₁] [":", expr «expr ≠ »((m.choose i : exprℂ()), 0)] [":=", expr nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (nat.choose_pos (nat.le_of_lt_succ (mem_range.1 hi))))],
   have [ident h₂] [] [":=", expr nat.choose_mul_factorial_mul_factorial «expr $ »(nat.le_of_lt_succ, finset.mem_range.1 hi)],
   rw ["[", "<-", expr h₂, ",", expr nat.cast_mul, ",", expr nat.cast_mul, ",", expr mul_inv₀, ",", expr mul_inv₀, "]"] [],
   simp [] [] ["only"] ["[", expr mul_left_comm (m.choose i : exprℂ()), ",", expr mul_assoc, ",", expr mul_left_comm «expr ⁻¹»((m.choose i : exprℂ())), ",", expr mul_comm (m.choose i : exprℂ()), "]"] [] [],
   rw [expr inv_mul_cancel h₁] [],
   simp [] [] [] ["[", expr div_eq_mul_inv, ",", expr mul_comm, ",", expr mul_assoc, ",", expr mul_left_comm, "]"] [] []
 end),
by rw [expr lim_mul_lim] []; exact [expr eq.symm (lim_eq_lim_of_equiv (by dsimp [] [] [] []; simp [] [] ["only"] ["[", expr hj, "]"] [] []; exact [expr cauchy_product (is_cau_abs_exp x) (is_cau_exp y)]))]

theorem exp_list_sum (l : List ℂ) : exp l.sum = (l.map exp).Prod :=
  @MonoidHom.map_list_prod (Multiplicative ℂ) ℂ _ _ ⟨exp, exp_zero, exp_add⟩ l

theorem exp_multiset_sum (s : Multiset ℂ) : exp s.sum = (s.map exp).Prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℂ) ℂ _ _ ⟨exp, exp_zero, exp_add⟩ s

theorem exp_sum {α : Type _} (s : Finset α) (f : α → ℂ) : exp (∑x in s, f x) = ∏x in s, exp (f x) :=
  @MonoidHom.map_prod (Multiplicative ℂ) α ℂ _ _ ⟨exp, exp_zero, exp_add⟩ f s

theorem exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp (n*x) = exp x ^ n
| 0 =>
  by 
    rw [Nat.cast_zero, zero_mul, exp_zero, pow_zeroₓ]
| Nat.succ n =>
  by 
    rw [pow_succ'ₓ, Nat.cast_add_one, add_mulₓ, exp_add, ←exp_nat_mul, one_mulₓ]

theorem exp_ne_zero : exp x ≠ 0 :=
  fun h =>
    zero_ne_one$
      by 
        rw [←exp_zero, ←add_neg_selfₓ x, exp_add, h] <;> simp 

theorem exp_neg : exp (-x) = exp x⁻¹ :=
  by 
    rw [←mul_right_inj' (exp_ne_zero x), ←exp_add] <;> simp [mul_inv_cancel (exp_ne_zero x)]

theorem exp_sub : exp (x - y) = exp x / exp y :=
  by 
    simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

theorem exp_int_mul (z : ℂ) (n : ℤ) : Complex.exp (n*z) = Complex.exp z ^ n :=
  by 
    cases n
    ·
      apply Complex.exp_nat_mul
    ·
      simpa [Complex.exp_neg, add_commₓ, ←neg_mul_eq_neg_mul_symm] using Complex.exp_nat_mul (-z) (1+n)

@[simp]
theorem exp_conj : exp (conj x) = conj (exp x) :=
  by 
    dsimp [exp]
    rw [←lim_conj]
    refine' congr_argₓ limₓ (CauSeq.ext fun _ => _)
    dsimp [exp', Function.comp, cau_seq_conj]
    rw [star_ring_aut.map_sum]
    refine' sum_congr rfl fun n hn => _ 
    rw [RingEquiv.map_div, RingEquiv.map_pow, ←of_real_nat_cast, conj_of_real]

@[simp]
theorem of_real_exp_of_real_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
  eq_conj_iff_re.1$
    by 
      rw [←exp_conj, conj_of_real]

@[simp, normCast]
theorem of_real_exp (x : ℝ) : (Real.exp x : ℂ) = exp x :=
  of_real_exp_of_real_re _

@[simp]
theorem exp_of_real_im (x : ℝ) : (exp x).im = 0 :=
  by 
    rw [←of_real_exp_of_real_re, of_real_im]

theorem exp_of_real_re (x : ℝ) : (exp x).re = Real.exp x :=
  rfl

theorem two_sinh : (2*sinh x) = exp x - exp (-x) :=
  mul_div_cancel' _ two_ne_zero'

theorem two_cosh : (2*cosh x) = exp x+exp (-x) :=
  mul_div_cancel' _ two_ne_zero'

@[simp]
theorem sinh_zero : sinh 0 = 0 :=
  by 
    simp [sinh]

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x :=
  by 
    simp [sinh, exp_neg, (neg_div _ _).symm, add_mulₓ]

private theorem sinh_add_aux {a b c d : ℂ} : (((a - b)*c+d)+(a+b)*c - d) = 2*(a*c) - b*d :=
  by 
    ring

theorem sinh_add : sinh (x+y) = (sinh x*cosh y)+cosh x*sinh y :=
  by 
    rw [←mul_right_inj' (@two_ne_zero' ℂ _ _ _), two_sinh, exp_add, neg_add, exp_add, eq_comm, mul_addₓ, ←mul_assocₓ,
      two_sinh, mul_left_commₓ, two_sinh, ←mul_right_inj' (@two_ne_zero' ℂ _ _ _), mul_addₓ, mul_left_commₓ, two_cosh,
      ←mul_assocₓ, two_cosh]
    exact sinh_add_aux

@[simp]
theorem cosh_zero : cosh 0 = 1 :=
  by 
    simp [cosh]

@[simp]
theorem cosh_neg : cosh (-x) = cosh x :=
  by 
    simp [add_commₓ, cosh, exp_neg]

private theorem cosh_add_aux {a b c d : ℂ} : (((a+b)*c+d)+(a - b)*c - d) = 2*(a*c)+b*d :=
  by 
    ring

theorem cosh_add : cosh (x+y) = (cosh x*cosh y)+sinh x*sinh y :=
  by 
    rw [←mul_right_inj' (@two_ne_zero' ℂ _ _ _), two_cosh, exp_add, neg_add, exp_add, eq_comm, mul_addₓ, ←mul_assocₓ,
      two_cosh, ←mul_assocₓ, two_sinh, ←mul_right_inj' (@two_ne_zero' ℂ _ _ _), mul_addₓ, mul_left_commₓ, two_cosh,
      mul_left_commₓ, two_sinh]
    exact cosh_add_aux

theorem sinh_sub : sinh (x - y) = (sinh x*cosh y) - cosh x*sinh y :=
  by 
    simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

theorem cosh_sub : cosh (x - y) = (cosh x*cosh y) - sinh x*sinh y :=
  by 
    simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

theorem sinh_conj : sinh (conj x) = conj (sinh x) :=
  by 
    rw [sinh, ←RingEquiv.map_neg, exp_conj, exp_conj, ←RingEquiv.map_sub, sinh, RingEquiv.map_div, conj_bit0,
      RingEquiv.map_one]

@[simp]
theorem of_real_sinh_of_real_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
  eq_conj_iff_re.1$
    by 
      rw [←sinh_conj, conj_of_real]

@[simp, normCast]
theorem of_real_sinh (x : ℝ) : (Real.sinh x : ℂ) = sinh x :=
  of_real_sinh_of_real_re _

@[simp]
theorem sinh_of_real_im (x : ℝ) : (sinh x).im = 0 :=
  by 
    rw [←of_real_sinh_of_real_re, of_real_im]

theorem sinh_of_real_re (x : ℝ) : (sinh x).re = Real.sinh x :=
  rfl

theorem cosh_conj : cosh (conj x) = conj (cosh x) :=
  by 
    rw [cosh, ←RingEquiv.map_neg, exp_conj, exp_conj, ←RingEquiv.map_add, cosh, RingEquiv.map_div, conj_bit0,
      RingEquiv.map_one]

@[simp]
theorem of_real_cosh_of_real_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
  eq_conj_iff_re.1$
    by 
      rw [←cosh_conj, conj_of_real]

@[simp, normCast]
theorem of_real_cosh (x : ℝ) : (Real.cosh x : ℂ) = cosh x :=
  of_real_cosh_of_real_re _

@[simp]
theorem cosh_of_real_im (x : ℝ) : (cosh x).im = 0 :=
  by 
    rw [←of_real_cosh_of_real_re, of_real_im]

theorem cosh_of_real_re (x : ℝ) : (cosh x).re = Real.cosh x :=
  rfl

theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  rfl

@[simp]
theorem tanh_zero : tanh 0 = 0 :=
  by 
    simp [tanh]

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x :=
  by 
    simp [tanh, neg_div]

theorem tanh_conj : tanh (conj x) = conj (tanh x) :=
  by 
    rw [tanh, sinh_conj, cosh_conj, ←RingEquiv.map_div, tanh]

@[simp]
theorem of_real_tanh_of_real_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
  eq_conj_iff_re.1$
    by 
      rw [←tanh_conj, conj_of_real]

@[simp, normCast]
theorem of_real_tanh (x : ℝ) : (Real.tanh x : ℂ) = tanh x :=
  of_real_tanh_of_real_re _

@[simp]
theorem tanh_of_real_im (x : ℝ) : (tanh x).im = 0 :=
  by 
    rw [←of_real_tanh_of_real_re, of_real_im]

theorem tanh_of_real_re (x : ℝ) : (tanh x).re = Real.tanh x :=
  rfl

theorem cosh_add_sinh : (cosh x+sinh x) = exp x :=
  by 
    rw [←mul_right_inj' (@two_ne_zero' ℂ _ _ _), mul_addₓ, two_cosh, two_sinh, add_add_sub_cancel, two_mul]

theorem sinh_add_cosh : (sinh x+cosh x) = exp x :=
  by 
    rw [add_commₓ, cosh_add_sinh]

theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) :=
  by 
    rw [←mul_right_inj' (@two_ne_zero' ℂ _ _ _), mul_sub, two_cosh, two_sinh, add_sub_sub_cancel, two_mul]

theorem cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 :=
  by 
    rw [sq_sub_sq, cosh_add_sinh, cosh_sub_sinh, ←exp_add, add_neg_selfₓ, exp_zero]

theorem cosh_sq : cosh x ^ 2 = (sinh x ^ 2)+1 :=
  by 
    rw [←cosh_sq_sub_sinh_sq x]
    ring

theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 :=
  by 
    rw [←cosh_sq_sub_sinh_sq x]
    ring

theorem cosh_two_mul : cosh (2*x) = (cosh x ^ 2)+sinh x ^ 2 :=
  by 
    rw [two_mul, cosh_add, sq, sq]

theorem sinh_two_mul : sinh (2*x) = (2*sinh x)*cosh x :=
  by 
    rw [two_mul, sinh_add]
    ring

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cosh_three_mul : «expr = »(cosh «expr * »(3, x), «expr - »(«expr * »(4, «expr ^ »(cosh x, 3)), «expr * »(3, cosh x))) :=
begin
  have [ident h1] [":", expr «expr = »(«expr + »(x, «expr * »(2, x)), «expr * »(3, x))] [],
  by ring [],
  rw ["[", "<-", expr h1, ",", expr cosh_add x «expr * »(2, x), "]"] [],
  simp [] [] ["only"] ["[", expr cosh_two_mul, ",", expr sinh_two_mul, "]"] [] [],
  have [ident h2] [":", expr «expr = »(«expr * »(sinh x, «expr * »(«expr * »(2, sinh x), cosh x)), «expr * »(«expr * »(2, cosh x), «expr ^ »(sinh x, 2)))] [],
  by ring [],
  rw ["[", expr h2, ",", expr sinh_sq, "]"] [],
  ring []
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sinh_three_mul : «expr = »(sinh «expr * »(3, x), «expr + »(«expr * »(4, «expr ^ »(sinh x, 3)), «expr * »(3, sinh x))) :=
begin
  have [ident h1] [":", expr «expr = »(«expr + »(x, «expr * »(2, x)), «expr * »(3, x))] [],
  by ring [],
  rw ["[", "<-", expr h1, ",", expr sinh_add x «expr * »(2, x), "]"] [],
  simp [] [] ["only"] ["[", expr cosh_two_mul, ",", expr sinh_two_mul, "]"] [] [],
  have [ident h2] [":", expr «expr = »(«expr * »(cosh x, «expr * »(«expr * »(2, sinh x), cosh x)), «expr * »(«expr * »(2, sinh x), «expr ^ »(cosh x, 2)))] [],
  by ring [],
  rw ["[", expr h2, ",", expr cosh_sq, "]"] [],
  ring []
end

@[simp]
theorem sin_zero : sin 0 = 0 :=
  by 
    simp [sin]

@[simp]
theorem sin_neg : sin (-x) = -sin x :=
  by 
    simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mulₓ]

theorem two_sin : (2*sin x) = (exp ((-x)*I) - exp (x*I))*I :=
  mul_div_cancel' _ two_ne_zero'

theorem two_cos : (2*cos x) = exp (x*I)+exp ((-x)*I) :=
  mul_div_cancel' _ two_ne_zero'

theorem sinh_mul_I : sinh (x*I) = sin x*I :=
  by 
    rw [←mul_right_inj' (@two_ne_zero' ℂ _ _ _), two_sinh, ←mul_assocₓ, two_sin, mul_assocₓ, I_mul_I, mul_neg_one,
      neg_sub, neg_mul_eq_neg_mul]

theorem cosh_mul_I : cosh (x*I) = cos x :=
  by 
    rw [←mul_right_inj' (@two_ne_zero' ℂ _ _ _), two_cosh, two_cos, neg_mul_eq_neg_mul]

theorem tanh_mul_I : tanh (x*I) = tan x*I :=
  by 
    rw [tanh_eq_sinh_div_cosh, cosh_mul_I, sinh_mul_I, mul_div_right_comm, tan]

theorem cos_mul_I : cos (x*I) = cosh x :=
  by 
    rw [←cosh_mul_I] <;> ringNF <;> simp 

theorem sin_mul_I : sin (x*I) = sinh x*I :=
  have h : (I*sin (x*I)) = -sinh x :=
    by 
      rw [mul_commₓ, ←sinh_mul_I]
      ringNF 
      simp 
  by 
    simpa only [neg_mul_eq_neg_mul_symm, div_I, neg_negₓ] using CancelFactors.cancel_factors_eq_div h I_ne_zero

theorem tan_mul_I : tan (x*I) = tanh x*I :=
  by 
    rw [tan, sin_mul_I, cos_mul_I, mul_div_right_comm, tanh_eq_sinh_div_cosh]

theorem sin_add : sin (x+y) = (sin x*cos y)+cos x*sin y :=
  by 
    rw [←mul_left_inj' I_ne_zero, ←sinh_mul_I, add_mulₓ, add_mulₓ, mul_right_commₓ, ←sinh_mul_I, mul_assocₓ,
      ←sinh_mul_I, ←cosh_mul_I, ←cosh_mul_I, sinh_add]

@[simp]
theorem cos_zero : cos 0 = 1 :=
  by 
    simp [cos]

@[simp]
theorem cos_neg : cos (-x) = cos x :=
  by 
    simp [cos, sub_eq_add_neg, exp_neg, add_commₓ]

private theorem cos_add_aux {a b c d : ℂ} : (((a+b)*c+d) - ((b - a)*d - c)*-1) = 2*(a*c)+b*d :=
  by 
    ring

theorem cos_add : cos (x+y) = (cos x*cos y) - sin x*sin y :=
  by 
    rw [←cosh_mul_I, add_mulₓ, cosh_add, cosh_mul_I, cosh_mul_I, sinh_mul_I, sinh_mul_I, mul_mul_mul_commₓ, I_mul_I,
      mul_neg_one, sub_eq_add_neg]

theorem sin_sub : sin (x - y) = (sin x*cos y) - cos x*sin y :=
  by 
    simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

theorem cos_sub : cos (x - y) = (cos x*cos y)+sin x*sin y :=
  by 
    simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

theorem sin_add_mul_I (x y : ℂ) : sin (x+y*I) = (sin x*cosh y)+(cos x*sinh y)*I :=
  by 
    rw [sin_add, cos_mul_I, sin_mul_I, mul_assocₓ]

theorem sin_eq (z : ℂ) : sin z = (sin z.re*cosh z.im)+(cos z.re*sinh z.im)*I :=
  by 
    convert sin_add_mul_I z.re z.im <;> exact (re_add_im z).symm

theorem cos_add_mul_I (x y : ℂ) : cos (x+y*I) = (cos x*cosh y) - (sin x*sinh y)*I :=
  by 
    rw [cos_add, cos_mul_I, sin_mul_I, mul_assocₓ]

theorem cos_eq (z : ℂ) : cos z = (cos z.re*cosh z.im) - (sin z.re*sinh z.im)*I :=
  by 
    convert cos_add_mul_I z.re z.im <;> exact (re_add_im z).symm

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sin_sub_sin : «expr = »(«expr - »(sin x, sin y), «expr * »(«expr * »(2, sin «expr / »(«expr - »(x, y), 2)), cos «expr / »(«expr + »(x, y), 2))) :=
begin
  have [ident s1] [] [":=", expr sin_add «expr / »(«expr + »(x, y), 2) «expr / »(«expr - »(x, y), 2)],
  have [ident s2] [] [":=", expr sin_sub «expr / »(«expr + »(x, y), 2) «expr / »(«expr - »(x, y), 2)],
  rw ["[", expr div_add_div_same, ",", expr add_sub, ",", expr add_right_comm, ",", expr add_sub_cancel, ",", expr half_add_self, "]"] ["at", ident s1],
  rw ["[", expr div_sub_div_same, ",", "<-", expr sub_add, ",", expr add_sub_cancel', ",", expr half_add_self, "]"] ["at", ident s2],
  rw ["[", expr s1, ",", expr s2, "]"] [],
  ring []
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cos_sub_cos : «expr = »(«expr - »(cos x, cos y), «expr * »(«expr * »(«expr- »(2), sin «expr / »(«expr + »(x, y), 2)), sin «expr / »(«expr - »(x, y), 2))) :=
begin
  have [ident s1] [] [":=", expr cos_add «expr / »(«expr + »(x, y), 2) «expr / »(«expr - »(x, y), 2)],
  have [ident s2] [] [":=", expr cos_sub «expr / »(«expr + »(x, y), 2) «expr / »(«expr - »(x, y), 2)],
  rw ["[", expr div_add_div_same, ",", expr add_sub, ",", expr add_right_comm, ",", expr add_sub_cancel, ",", expr half_add_self, "]"] ["at", ident s1],
  rw ["[", expr div_sub_div_same, ",", "<-", expr sub_add, ",", expr add_sub_cancel', ",", expr half_add_self, "]"] ["at", ident s2],
  rw ["[", expr s1, ",", expr s2, "]"] [],
  ring []
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cos_add_cos : «expr = »(«expr + »(cos x, cos y), «expr * »(«expr * »(2, cos «expr / »(«expr + »(x, y), 2)), cos «expr / »(«expr - »(x, y), 2))) :=
begin
  have [ident h2] [":", expr «expr ≠ »((2 : exprℂ()), 0)] [":=", expr by norm_num [] []],
  calc
    «expr = »(«expr + »(cos x, cos y), «expr + »(cos «expr + »(«expr / »(«expr + »(x, y), 2), «expr / »(«expr - »(x, y), 2)), cos «expr - »(«expr / »(«expr + »(x, y), 2), «expr / »(«expr - »(x, y), 2)))) : _
    «expr = »(..., «expr + »(«expr - »(«expr * »(cos «expr / »(«expr + »(x, y), 2), cos «expr / »(«expr - »(x, y), 2)), «expr * »(sin «expr / »(«expr + »(x, y), 2), sin «expr / »(«expr - »(x, y), 2))), «expr + »(«expr * »(cos «expr / »(«expr + »(x, y), 2), cos «expr / »(«expr - »(x, y), 2)), «expr * »(sin «expr / »(«expr + »(x, y), 2), sin «expr / »(«expr - »(x, y), 2))))) : _
    «expr = »(..., «expr * »(«expr * »(2, cos «expr / »(«expr + »(x, y), 2)), cos «expr / »(«expr - »(x, y), 2))) : _,
  { congr; field_simp [] ["[", expr h2, "]"] [] []; ring [] },
  { rw ["[", expr cos_add, ",", expr cos_sub, "]"] [] },
  ring []
end

theorem sin_conj : sin (conj x) = conj (sin x) :=
  by 
    rw [←mul_left_inj' I_ne_zero, ←sinh_mul_I, ←conj_neg_I, ←RingEquiv.map_mul, ←RingEquiv.map_mul, sinh_conj,
      mul_neg_eq_neg_mul_symm, sinh_neg, sinh_mul_I, mul_neg_eq_neg_mul_symm]

@[simp]
theorem of_real_sin_of_real_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
  eq_conj_iff_re.1$
    by 
      rw [←sin_conj, conj_of_real]

@[simp, normCast]
theorem of_real_sin (x : ℝ) : (Real.sin x : ℂ) = sin x :=
  of_real_sin_of_real_re _

@[simp]
theorem sin_of_real_im (x : ℝ) : (sin x).im = 0 :=
  by 
    rw [←of_real_sin_of_real_re, of_real_im]

theorem sin_of_real_re (x : ℝ) : (sin x).re = Real.sin x :=
  rfl

theorem cos_conj : cos (conj x) = conj (cos x) :=
  by 
    rw [←cosh_mul_I, ←conj_neg_I, ←RingEquiv.map_mul, ←cosh_mul_I, cosh_conj, mul_neg_eq_neg_mul_symm, cosh_neg]

@[simp]
theorem of_real_cos_of_real_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
  eq_conj_iff_re.1$
    by 
      rw [←cos_conj, conj_of_real]

@[simp, normCast]
theorem of_real_cos (x : ℝ) : (Real.cos x : ℂ) = cos x :=
  of_real_cos_of_real_re _

@[simp]
theorem cos_of_real_im (x : ℝ) : (cos x).im = 0 :=
  by 
    rw [←of_real_cos_of_real_re, of_real_im]

theorem cos_of_real_re (x : ℝ) : (cos x).re = Real.cos x :=
  rfl

@[simp]
theorem tan_zero : tan 0 = 0 :=
  by 
    simp [tan]

theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  rfl

theorem tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : (tan x*cos x) = sin x :=
  by 
    rw [tan_eq_sin_div_cos, div_mul_cancel _ hx]

@[simp]
theorem tan_neg : tan (-x) = -tan x :=
  by 
    simp [tan, neg_div]

theorem tan_conj : tan (conj x) = conj (tan x) :=
  by 
    rw [tan, sin_conj, cos_conj, ←RingEquiv.map_div, tan]

@[simp]
theorem of_real_tan_of_real_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
  eq_conj_iff_re.1$
    by 
      rw [←tan_conj, conj_of_real]

@[simp, normCast]
theorem of_real_tan (x : ℝ) : (Real.tan x : ℂ) = tan x :=
  of_real_tan_of_real_re _

@[simp]
theorem tan_of_real_im (x : ℝ) : (tan x).im = 0 :=
  by 
    rw [←of_real_tan_of_real_re, of_real_im]

theorem tan_of_real_re (x : ℝ) : (tan x).re = Real.tan x :=
  rfl

theorem cos_add_sin_I : (cos x+sin x*I) = exp (x*I) :=
  by 
    rw [←cosh_add_sinh, sinh_mul_I, cosh_mul_I]

theorem cos_sub_sin_I : (cos x - sin x*I) = exp ((-x)*I) :=
  by 
    rw [←neg_mul_eq_neg_mul, ←cosh_sub_sinh, sinh_mul_I, cosh_mul_I]

@[simp]
theorem sin_sq_add_cos_sq : ((sin x ^ 2)+cos x ^ 2) = 1 :=
  Eq.trans
    (by 
      rw [cosh_mul_I, sinh_mul_I, mul_powₓ, I_sq, mul_neg_one, sub_neg_eq_add, add_commₓ])
    (cosh_sq_sub_sinh_sq (x*I))

@[simp]
theorem cos_sq_add_sin_sq : ((cos x ^ 2)+sin x ^ 2) = 1 :=
  by 
    rw [add_commₓ, sin_sq_add_cos_sq]

theorem cos_two_mul' : cos (2*x) = cos x ^ 2 - sin x ^ 2 :=
  by 
    rw [two_mul, cos_add, ←sq, ←sq]

theorem cos_two_mul : cos (2*x) = (2*cos x ^ 2) - 1 :=
  by 
    rw [cos_two_mul', eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x), ←sub_add, sub_add_eq_add_sub, two_mul]

theorem sin_two_mul : sin (2*x) = (2*sin x)*cos x :=
  by 
    rw [two_mul, sin_add, two_mul, add_mulₓ, mul_commₓ]

theorem cos_sq : cos x ^ 2 = (1 / 2)+cos (2*x) / 2 :=
  by 
    simp [cos_two_mul, div_add_div_same, mul_div_cancel_left, two_ne_zero', -one_div]

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 :=
  by 
    rw [←sin_sq_add_cos_sq x, add_sub_cancel']

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
  by 
    rw [←sin_sq_add_cos_sq x, add_sub_cancel]

theorem inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (1+tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have  : cos x ^ 2 ≠ 0 := pow_ne_zero 2 hx 
  by 
    rw [tan_eq_sin_div_cos, div_pow]
    fieldSimp [this]

theorem tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (tan x ^ 2 / 1+tan x ^ 2) = sin x ^ 2 :=
  by 
    simp only [←tan_mul_cos hx, mul_powₓ, ←inv_one_add_tan_sq hx, div_eq_mul_inv, one_mulₓ]

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cos_three_mul : «expr = »(cos «expr * »(3, x), «expr - »(«expr * »(4, «expr ^ »(cos x, 3)), «expr * »(3, cos x))) :=
begin
  have [ident h1] [":", expr «expr = »(«expr + »(x, «expr * »(2, x)), «expr * »(3, x))] [],
  by ring [],
  rw ["[", "<-", expr h1, ",", expr cos_add x «expr * »(2, x), "]"] [],
  simp [] [] ["only"] ["[", expr cos_two_mul, ",", expr sin_two_mul, ",", expr mul_add, ",", expr mul_sub, ",", expr mul_one, ",", expr sq, "]"] [] [],
  have [ident h2] [":", expr «expr = »(«expr * »(4, «expr ^ »(cos x, 3)), «expr + »(«expr * »(«expr * »(«expr * »(2, cos x), cos x), cos x), «expr * »(«expr * »(2, cos x), «expr ^ »(cos x, 2))))] [],
  by ring [],
  rw ["[", expr h2, ",", expr cos_sq', "]"] [],
  ring []
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sin_three_mul : «expr = »(sin «expr * »(3, x), «expr - »(«expr * »(3, sin x), «expr * »(4, «expr ^ »(sin x, 3)))) :=
begin
  have [ident h1] [":", expr «expr = »(«expr + »(x, «expr * »(2, x)), «expr * »(3, x))] [],
  by ring [],
  rw ["[", "<-", expr h1, ",", expr sin_add x «expr * »(2, x), "]"] [],
  simp [] [] ["only"] ["[", expr cos_two_mul, ",", expr sin_two_mul, ",", expr cos_sq', "]"] [] [],
  have [ident h2] [":", expr «expr = »(«expr * »(cos x, «expr * »(«expr * »(2, sin x), cos x)), «expr * »(«expr * »(2, sin x), «expr ^ »(cos x, 2)))] [],
  by ring [],
  rw ["[", expr h2, ",", expr cos_sq', "]"] [],
  ring []
end

theorem exp_mul_I : exp (x*I) = cos x+sin x*I :=
  (cos_add_sin_I _).symm

theorem exp_add_mul_I : exp (x+y*I) = exp x*cos y+sin y*I :=
  by 
    rw [exp_add, exp_mul_I]

theorem exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re*cos x.im+sin x.im*I :=
  by 
    rw [←exp_add_mul_I, re_add_im]

theorem exp_re : (exp x).re = Real.exp x.re*Real.cos x.im :=
  by 
    rw [exp_eq_exp_re_mul_sin_add_cos]
    simp [exp_of_real_re, cos_of_real_re]

theorem exp_im : (exp x).im = Real.exp x.re*Real.sin x.im :=
  by 
    rw [exp_eq_exp_re_mul_sin_add_cos]
    simp [exp_of_real_re, sin_of_real_re]

@[simp]
theorem exp_of_real_mul_I_re (x : ℝ) : (exp (x*I)).re = Real.cos x :=
  by 
    simp [exp_mul_I, cos_of_real_re]

@[simp]
theorem exp_of_real_mul_I_im (x : ℝ) : (exp (x*I)).im = Real.sin x :=
  by 
    simp [exp_mul_I, sin_of_real_re]

/-- **De Moivre's formula** -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) : (cos z+sin z*I) ^ n = cos («expr↑ » n*z)+sin («expr↑ » n*z)*I :=
  by 
    rw [←exp_mul_I, ←exp_mul_I]
    induction' n with n ih
    ·
      rw [pow_zeroₓ, Nat.cast_zero, zero_mul, zero_mul, exp_zero]
    ·
      rw [pow_succ'ₓ, ih, Nat.cast_succ, add_mulₓ, add_mulₓ, one_mulₓ, exp_add]

end Complex

namespace Real

open Complex

variable (x y : ℝ)

@[simp]
theorem exp_zero : exp 0 = 1 :=
  by 
    simp [Real.exp]

theorem exp_add : exp (x+y) = exp x*exp y :=
  by 
    simp [exp_add, exp]

theorem exp_list_sum (l : List ℝ) : exp l.sum = (l.map exp).Prod :=
  @MonoidHom.map_list_prod (Multiplicative ℝ) ℝ _ _ ⟨exp, exp_zero, exp_add⟩ l

theorem exp_multiset_sum (s : Multiset ℝ) : exp s.sum = (s.map exp).Prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℝ) ℝ _ _ ⟨exp, exp_zero, exp_add⟩ s

theorem exp_sum {α : Type _} (s : Finset α) (f : α → ℝ) : exp (∑x in s, f x) = ∏x in s, exp (f x) :=
  @MonoidHom.map_prod (Multiplicative ℝ) α ℝ _ _ ⟨exp, exp_zero, exp_add⟩ f s

theorem exp_nat_mul (x : ℝ) : ∀ n : ℕ, exp (n*x) = exp x ^ n
| 0 =>
  by 
    rw [Nat.cast_zero, zero_mul, exp_zero, pow_zeroₓ]
| Nat.succ n =>
  by 
    rw [pow_succ'ₓ, Nat.cast_add_one, add_mulₓ, exp_add, ←exp_nat_mul, one_mulₓ]

theorem exp_ne_zero : exp x ≠ 0 :=
  fun h =>
    exp_ne_zero x$
      by 
        rw [exp, ←of_real_inj] at h <;> simp_all 

theorem exp_neg : exp (-x) = exp x⁻¹ :=
  by 
    rw [←of_real_inj, exp, of_real_exp_of_real_re, of_real_neg, exp_neg, of_real_inv, of_real_exp]

theorem exp_sub : exp (x - y) = exp x / exp y :=
  by 
    simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

@[simp]
theorem sin_zero : sin 0 = 0 :=
  by 
    simp [sin]

@[simp]
theorem sin_neg : sin (-x) = -sin x :=
  by 
    simp [sin, exp_neg, (neg_div _ _).symm, add_mulₓ]

theorem sin_add : sin (x+y) = (sin x*cos y)+cos x*sin y :=
  by 
    rw [←of_real_inj] <;> simp [sin, sin_add]

@[simp]
theorem cos_zero : cos 0 = 1 :=
  by 
    simp [cos]

@[simp]
theorem cos_neg : cos (-x) = cos x :=
  by 
    simp [cos, exp_neg]

theorem cos_add : cos (x+y) = (cos x*cos y) - sin x*sin y :=
  by 
    rw [←of_real_inj] <;> simp [cos, cos_add]

theorem sin_sub : sin (x - y) = (sin x*cos y) - cos x*sin y :=
  by 
    simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

theorem cos_sub : cos (x - y) = (cos x*cos y)+sin x*sin y :=
  by 
    simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

theorem sin_sub_sin : sin x - sin y = (2*sin ((x - y) / 2))*cos ((x+y) / 2) :=
  by 
    rw [←of_real_inj]
    simp only [sin, cos, of_real_sin_of_real_re, of_real_sub, of_real_add, of_real_div, of_real_mul, of_real_one,
      of_real_bit0]
    convert sin_sub_sin _ _ <;> normCast

theorem cos_sub_cos : cos x - cos y = ((-2)*sin ((x+y) / 2))*sin ((x - y) / 2) :=
  by 
    rw [←of_real_inj]
    simp only [cos, neg_mul_eq_neg_mul_symm, of_real_sin, of_real_sub, of_real_add, of_real_cos_of_real_re, of_real_div,
      of_real_mul, of_real_one, of_real_neg, of_real_bit0]
    convert cos_sub_cos _ _ 
    ring

theorem cos_add_cos : (cos x+cos y) = (2*cos ((x+y) / 2))*cos ((x - y) / 2) :=
  by 
    rw [←of_real_inj]
    simp only [cos, of_real_sub, of_real_add, of_real_cos_of_real_re, of_real_div, of_real_mul, of_real_one,
      of_real_bit0]
    convert cos_add_cos _ _ <;> normCast

theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  by 
    rw [←of_real_inj, of_real_tan, tan_eq_sin_div_cos, of_real_div, of_real_sin, of_real_cos]

theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : (tan x*cos x) = sin x :=
  by 
    rw [tan_eq_sin_div_cos, div_mul_cancel _ hx]

@[simp]
theorem tan_zero : tan 0 = 0 :=
  by 
    simp [tan]

@[simp]
theorem tan_neg : tan (-x) = -tan x :=
  by 
    simp [tan, neg_div]

@[simp]
theorem sin_sq_add_cos_sq : ((sin x ^ 2)+cos x ^ 2) = 1 :=
  of_real_inj.1$
    by 
      simp 

@[simp]
theorem cos_sq_add_sin_sq : ((cos x ^ 2)+sin x ^ 2) = 1 :=
  by 
    rw [add_commₓ, sin_sq_add_cos_sq]

theorem sin_sq_le_one : sin x ^ 2 ≤ 1 :=
  by 
    rw [←sin_sq_add_cos_sq x] <;> exact le_add_of_nonneg_right (sq_nonneg _)

theorem cos_sq_le_one : cos x ^ 2 ≤ 1 :=
  by 
    rw [←sin_sq_add_cos_sq x] <;> exact le_add_of_nonneg_left (sq_nonneg _)

theorem abs_sin_le_one : |sin x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2$
    by 
      simp only [←sq, sin_sq_le_one]

theorem abs_cos_le_one : |cos x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2$
    by 
      simp only [←sq, cos_sq_le_one]

theorem sin_le_one : sin x ≤ 1 :=
  (abs_le.1 (abs_sin_le_one _)).2

theorem cos_le_one : cos x ≤ 1 :=
  (abs_le.1 (abs_cos_le_one _)).2

theorem neg_one_le_sin : -1 ≤ sin x :=
  (abs_le.1 (abs_sin_le_one _)).1

theorem neg_one_le_cos : -1 ≤ cos x :=
  (abs_le.1 (abs_cos_le_one _)).1

theorem cos_two_mul : cos (2*x) = (2*cos x ^ 2) - 1 :=
  by 
    rw [←of_real_inj] <;> simp [cos_two_mul]

theorem cos_two_mul' : cos (2*x) = cos x ^ 2 - sin x ^ 2 :=
  by 
    rw [←of_real_inj] <;> simp [cos_two_mul']

theorem sin_two_mul : sin (2*x) = (2*sin x)*cos x :=
  by 
    rw [←of_real_inj] <;> simp [sin_two_mul]

theorem cos_sq : cos x ^ 2 = (1 / 2)+cos (2*x) / 2 :=
  of_real_inj.1$
    by 
      simpa using cos_sq x

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 :=
  by 
    rw [←sin_sq_add_cos_sq x, add_sub_cancel']

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
  eq_sub_iff_add_eq.2$ sin_sq_add_cos_sq _

theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) : |sin x| = sqrt (1 - cos x ^ 2) :=
  by 
    rw [←sin_sq, sqrt_sq_eq_abs]

theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) : |cos x| = sqrt (1 - sin x ^ 2) :=
  by 
    rw [←cos_sq', sqrt_sq_eq_abs]

theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1+tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have  : Complex.cos x ≠ 0 := mt (congr_argₓ re) hx 
  of_real_inj.1$
    by 
      simpa using Complex.inv_one_add_tan_sq this

theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (tan x ^ 2 / 1+tan x ^ 2) = sin x ^ 2 :=
  by 
    simp only [←tan_mul_cos hx, mul_powₓ, ←inv_one_add_tan_sq hx, div_eq_mul_inv, one_mulₓ]

theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : sqrt (1+tan x ^ 2)⁻¹ = cos x :=
  by 
    rw [←sqrt_sq hx.le, ←sqrt_inv, inv_one_add_tan_sq hx.ne']

theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : tan x / sqrt (1+tan x ^ 2) = sin x :=
  by 
    rw [←tan_mul_cos hx.ne', ←inv_sqrt_one_add_tan_sq hx, div_eq_mul_inv]

theorem cos_three_mul : cos (3*x) = (4*cos x ^ 3) - 3*cos x :=
  by 
    rw [←of_real_inj] <;> simp [cos_three_mul]

theorem sin_three_mul : sin (3*x) = (3*sin x) - 4*sin x ^ 3 :=
  by 
    rw [←of_real_inj] <;> simp [sin_three_mul]

/-- The definition of `sinh` in terms of `exp`. -/
theorem sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero$
    by 
      rw [sinh, exp, exp, Complex.of_real_neg, Complex.sinh, mul_two, ←Complex.add_re, ←mul_two,
        div_mul_cancel _ (two_ne_zero' : (2 : ℂ) ≠ 0), Complex.sub_re]

@[simp]
theorem sinh_zero : sinh 0 = 0 :=
  by 
    simp [sinh]

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x :=
  by 
    simp [sinh, exp_neg, (neg_div _ _).symm, add_mulₓ]

theorem sinh_add : sinh (x+y) = (sinh x*cosh y)+cosh x*sinh y :=
  by 
    rw [←of_real_inj] <;> simp [sinh_add]

/-- The definition of `cosh` in terms of `exp`. -/
theorem cosh_eq (x : ℝ) : cosh x = (exp x+exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero$
    by 
      rw [cosh, exp, exp, Complex.of_real_neg, Complex.cosh, mul_two, ←Complex.add_re, ←mul_two,
        div_mul_cancel _ (two_ne_zero' : (2 : ℂ) ≠ 0), Complex.add_re]

@[simp]
theorem cosh_zero : cosh 0 = 1 :=
  by 
    simp [cosh]

@[simp]
theorem cosh_neg : cosh (-x) = cosh x :=
  by 
    simp [cosh, exp_neg]

theorem cosh_add : cosh (x+y) = (cosh x*cosh y)+sinh x*sinh y :=
  by 
    rw [←of_real_inj] <;> simp [cosh, cosh_add]

theorem sinh_sub : sinh (x - y) = (sinh x*cosh y) - cosh x*sinh y :=
  by 
    simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

theorem cosh_sub : cosh (x - y) = (cosh x*cosh y) - sinh x*sinh y :=
  by 
    simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  of_real_inj.1$
    by 
      simp [tanh_eq_sinh_div_cosh]

@[simp]
theorem tanh_zero : tanh 0 = 0 :=
  by 
    simp [tanh]

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x :=
  by 
    simp [tanh, neg_div]

theorem cosh_add_sinh : (cosh x+sinh x) = exp x :=
  by 
    rw [←of_real_inj] <;> simp [cosh_add_sinh]

theorem sinh_add_cosh : (sinh x+cosh x) = exp x :=
  by 
    rw [←of_real_inj] <;> simp [sinh_add_cosh]

theorem cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 :=
  by 
    rw [←of_real_inj] <;> simp [cosh_sq_sub_sinh_sq]

theorem cosh_sq : cosh x ^ 2 = (sinh x ^ 2)+1 :=
  by 
    rw [←of_real_inj] <;> simp [cosh_sq]

theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 :=
  by 
    rw [←of_real_inj] <;> simp [sinh_sq]

theorem cosh_two_mul : cosh (2*x) = (cosh x ^ 2)+sinh x ^ 2 :=
  by 
    rw [←of_real_inj] <;> simp [cosh_two_mul]

theorem sinh_two_mul : sinh (2*x) = (2*sinh x)*cosh x :=
  by 
    rw [←of_real_inj] <;> simp [sinh_two_mul]

theorem cosh_three_mul : cosh (3*x) = (4*cosh x ^ 3) - 3*cosh x :=
  by 
    rw [←of_real_inj] <;> simp [cosh_three_mul]

theorem sinh_three_mul : sinh (3*x) = (4*sinh x ^ 3)+3*sinh x :=
  by 
    rw [←of_real_inj] <;> simp [sinh_three_mul]

open IsAbsoluteValue

/-- This is an intermediate result that is later replaced by `real.add_one_le_exp`; use that lemma
instead. -/
theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (x+1) ≤ exp x :=
  calc (x+1) ≤ limₓ (⟨fun n : ℕ => ((exp' x) n).re, is_cau_seq_re (exp' x)⟩ : CauSeq ℝ HasAbs.abs) :=
    le_lim
      (CauSeq.le_of_exists
        ⟨2,
          fun j hj =>
            show (x+(1 : ℝ)) ≤ (∑m in range j, (x ^ m / m ! : ℂ)).re from
              have h₁ : (((fun m : ℕ => (x ^ m / m ! : ℂ)) ∘ Nat.succ) 0).re = x :=
                by 
                  simp 
              have h₂ : ((x : ℂ) ^ 0 / 0!).re = 1 :=
                by 
                  simp 
              by 
                rw [←tsub_add_cancel_of_le hj, sum_range_succ', sum_range_succ', add_re, add_re, h₁, h₂, add_assocₓ,
                  ←coe_re_add_group_hom, re_add_group_hom.map_sum, coe_re_add_group_hom]
                refine' le_add_of_nonneg_of_le (sum_nonneg fun m hm => _) (le_reflₓ _)
                rw [←of_real_pow, ←of_real_nat_cast, ←of_real_div, of_real_re]
                exact div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)⟩)
    _ = exp x :=
    by 
      rw [exp, Complex.exp, ←cau_seq_re, lim_re]
    

theorem one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x :=
  by 
    linarith [add_one_le_exp_of_nonneg hx]

theorem exp_pos (x : ℝ) : 0 < exp x :=
  (le_totalₓ 0 x).elim (lt_of_lt_of_leₓ zero_lt_one ∘ one_le_exp)
    fun h =>
      by 
        rw [←neg_negₓ x, Real.exp_neg] <;> exact inv_pos.2 (lt_of_lt_of_leₓ zero_lt_one (one_le_exp (neg_nonneg.2 h)))

@[simp]
theorem abs_exp (x : ℝ) : |exp x| = exp x :=
  abs_of_pos (exp_pos _)

theorem exp_strict_mono : StrictMono exp :=
  fun x y h =>
    by 
      rw [←sub_add_cancel y x, Real.exp_add] <;>
        exact
          (lt_mul_iff_one_lt_left (exp_pos _)).2
            (lt_of_lt_of_leₓ
              (by 
                linarith)
              (add_one_le_exp_of_nonneg
                (by 
                  linarith)))

@[mono]
theorem exp_monotone : ∀ {x y : ℝ}, x ≤ y → exp x ≤ exp y :=
  exp_strict_mono.Monotone

@[simp]
theorem exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y :=
  exp_strict_mono.lt_iff_lt

@[simp]
theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
  exp_strict_mono.le_iff_le

theorem exp_injective : Function.Injective exp :=
  exp_strict_mono.Injective

@[simp]
theorem exp_eq_exp {x y : ℝ} : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff

@[simp]
theorem exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
  by 
    rw [←exp_zero, exp_injective.eq_iff]

@[simp]
theorem one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x :=
  by 
    rw [←exp_zero, exp_lt_exp]

@[simp]
theorem exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 :=
  by 
    rw [←exp_zero, exp_lt_exp]

@[simp]
theorem exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero ▸ exp_le_exp

@[simp]
theorem one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero ▸ exp_le_exp

/-- `real.cosh` is always positive -/
theorem cosh_pos (x : ℝ) : 0 < Real.cosh x :=
  (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

end Real

namespace Complex

theorem sum_div_factorial_le {α : Type _} [LinearOrderedField α] (n j : ℕ) (hn : 0 < n) :
  (∑m in Filter (fun k => n ≤ k) (range j), (1 / m ! : α)) ≤ n.succ / n !*n :=
  calc (∑m in Filter (fun k => n ≤ k) (range j), (1 / m ! : α)) = ∑m in range (j - n), 1 / (m+n)! :=
    sum_bij (fun m _ => m - n)
      (fun m hm =>
        mem_range.2$
          (tsub_lt_tsub_iff_right
                (by 
                  simp  at hm <;> tauto)).2
            (by 
              simp  at hm <;> tauto))
      (fun m hm =>
        by 
          rw [tsub_add_cancel_of_le] <;> simp  at * <;> tauto)
      (fun a₁ a₂ ha₁ ha₂ h =>
        by 
          rwa [tsub_eq_iff_eq_add_of_le, tsub_add_eq_add_tsub, eq_comm, tsub_eq_iff_eq_add_of_le, add_left_injₓ,
              eq_comm] at h <;>
            simp  at * <;> tauto)
      fun b hb =>
        ⟨b+n, mem_filter.2 ⟨mem_range.2$ lt_tsub_iff_right.mp (mem_range.1 hb), Nat.le_add_leftₓ _ _⟩,
          by 
            rw [add_tsub_cancel_right]⟩
    _ ≤ ∑m in range (j - n), (n !*n.succ ^ m)⁻¹ :=
    by 
      refine' sum_le_sum fun m n => _ 
      rw [one_div, inv_le_inv]
      ·
        rw [←Nat.cast_pow, ←Nat.cast_mul, Nat.cast_le, add_commₓ]
        exact Nat.factorial_mul_pow_le_factorial
      ·
        exact Nat.cast_pos.2 (Nat.factorial_pos _)
      ·
        exact mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) (pow_pos (Nat.cast_pos.2 (Nat.succ_posₓ _)) _)
    _ = n !⁻¹*∑m in range (j - n), n.succ⁻¹ ^ m :=
    by 
      simp [mul_inv₀, mul_sum.symm, sum_mul.symm, -Nat.factorial_succ, mul_commₓ, inv_pow₀]
    _ = (n.succ - n.succ*n.succ⁻¹ ^ (j - n)) / n !*n :=
    have h₁ : (n.succ : α) ≠ 1 := @Nat.cast_one α _ _ ▸ mt Nat.cast_inj.1 (mt Nat.succ.injₓ (pos_iff_ne_zero.1 hn))
    have h₂ : (n.succ : α) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    have h₃ : (n !*n : α) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.factorial_pos _)))
        (Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 hn))
    have h₄ : (n.succ - 1 : α) = n :=
      by 
        simp 
    by 
      rw [←geom_sum_def, geom_sum_inv h₁ h₂, eq_div_iff_mul_eq h₃, mul_commₓ _ (n !*n : α), ←mul_assocₓ (n !⁻¹ : α),
          ←mul_inv_rev₀, h₄, ←mul_assocₓ (n !*n : α), mul_commₓ (n : α) n !, mul_inv_cancel h₃] <;>
        simp [mul_addₓ, add_mulₓ, mul_assocₓ, mul_commₓ]
    _ ≤ n.succ / n !*n :=
    by 
      refine' Iff.mpr (div_le_div_right (mul_pos _ _)) _ 
      exact Nat.cast_pos.2 (Nat.factorial_pos _)
      exact Nat.cast_pos.2 hn 
      exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _))
    

theorem exp_bound {x : ℂ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) :
  abs (exp x - ∑m in range n, x ^ m / m !) ≤ (abs x ^ n)*n.succ*(n !*n)⁻¹ :=
  by 
    rw [←lim_const (∑m in range n, _), exp, sub_eq_add_neg, ←lim_neg, lim_add, ←lim_abs]
    refine' lim_le (CauSeq.le_of_exists ⟨n, fun j hj => _⟩)
    simpRw [←sub_eq_add_neg]
    show abs ((∑m in range j, x ^ m / m !) - ∑m in range n, x ^ m / m !) ≤ (abs x ^ n)*n.succ*(n !*n)⁻¹
    rw [sum_range_sub_sum_range hj]
    calc
      abs (∑m in (range j).filter fun k => n ≤ k, (x ^ m / m ! : ℂ)) =
        abs (∑m in (range j).filter fun k => n ≤ k, ((x ^ n)*x ^ (m - n) / m ! : ℂ)) :=
      by 
        refine' congr_argₓ abs (sum_congr rfl fun m hm => _)
        rw [mem_filter, mem_range] at hm 
        rw [←mul_div_assoc, ←pow_addₓ,
          add_tsub_cancel_of_le hm.2]_ ≤ ∑m in Filter (fun k => n ≤ k) (range j), abs ((x ^ n)*_ / m !) :=
      abv_sum_le_sum_abv _ _ _ ≤ ∑m in Filter (fun k => n ≤ k) (range j), (abs x ^ n)*1 / m ! :=
      by 
        refine' sum_le_sum fun m hm => _ 
        rw [abs_mul, abv_pow abs, abs_div, abs_cast_nat]
        refine' mul_le_mul_of_nonneg_left ((div_le_div_right _).2 _) _
        ·
          exact Nat.cast_pos.2 (Nat.factorial_pos _)
        ·
          rw [abv_pow abs]
          exact pow_le_one _ (abs_nonneg _) hx
        ·
          exact pow_nonneg (abs_nonneg _) _ _ = (abs x ^ n)*∑m in (range j).filter fun k => n ≤ k, (1 / m ! : ℝ) :=
      by 
        simp [abs_mul, abv_pow abs, abs_div, mul_sum.symm]_ ≤ (abs x ^ n)*n.succ*(n !*n)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_div_factorial_le _ _ hn) (pow_nonneg (abs_nonneg _) _)

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_bound'
{x : exprℂ()}
{n : exprℕ()}
(hx : «expr ≤ »(«expr / »(abs x, n.succ), «expr / »(1, 2))) : «expr ≤ »(abs «expr - »(exp x, «expr∑ in , »((m), range n, «expr / »(«expr ^ »(x, m), «expr !»(m)))), «expr * »(«expr / »(«expr ^ »(abs x, n), «expr !»(n)), 2)) :=
begin
  rw ["[", "<-", expr lim_const «expr∑ in , »((m), range n, _), ",", expr exp, ",", expr sub_eq_add_neg, ",", "<-", expr lim_neg, ",", expr lim_add, ",", "<-", expr lim_abs, "]"] [],
  refine [expr lim_le (cau_seq.le_of_exists ⟨n, λ j hj, _⟩)],
  simp_rw ["[", "<-", expr sub_eq_add_neg, "]"] [],
  show [expr «expr ≤ »(abs «expr - »(«expr∑ in , »((m), range j, «expr / »(«expr ^ »(x, m), «expr !»(m))), «expr∑ in , »((m), range n, «expr / »(«expr ^ »(x, m), «expr !»(m)))), «expr * »(«expr / »(«expr ^ »(abs x, n), «expr !»(n)), 2))],
  let [ident k] [] [":=", expr «expr - »(j, n)],
  have [ident hj] [":", expr «expr = »(j, «expr + »(n, k))] [":=", expr (add_tsub_cancel_of_le hj).symm],
  rw ["[", expr hj, ",", expr sum_range_add_sub_sum_range, "]"] [],
  calc
    «expr ≤ »(abs «expr∑ in , »((i : exprℕ()), range k, «expr / »(«expr ^ »(x, «expr + »(n, i)), («expr !»(«expr + »(n, i)) : exprℂ()))), «expr∑ in , »((i : exprℕ()), range k, abs «expr / »(«expr ^ »(x, «expr + »(n, i)), («expr !»(«expr + »(n, i)) : exprℂ())))) : abv_sum_le_sum_abv _ _
    «expr ≤ »(..., «expr∑ in , »((i : exprℕ()), range k, «expr / »(«expr ^ »(abs x, «expr + »(n, i)), «expr !»(«expr + »(n, i))))) : by simp [] [] ["only"] ["[", expr complex.abs_cast_nat, ",", expr complex.abs_div, ",", expr abv_pow abs, "]"] [] []
    «expr ≤ »(..., «expr∑ in , »((i : exprℕ()), range k, «expr / »(«expr ^ »(abs x, «expr + »(n, i)), «expr * »(«expr !»(n), «expr ^ »(n.succ, i))))) : _
    «expr = »(..., «expr∑ in , »((i : exprℕ()), range k, «expr * »(«expr / »(«expr ^ »(abs x, n), «expr !»(n)), «expr / »(«expr ^ »(abs x, i), «expr ^ »(n.succ, i))))) : _
    «expr ≤ »(..., «expr * »(«expr / »(«expr ^ »(abs x, n), «expr↑ »(«expr !»(n))), 2)) : _,
  { refine [expr sum_le_sum (λ m hm, div_le_div (pow_nonneg (abs_nonneg x) «expr + »(n, m)) (le_refl _) _ _)],
    { exact_mod_cast [expr mul_pos n.factorial_pos (pow_pos n.succ_pos _)] },
    { exact_mod_cast [expr nat.factorial_mul_pow_le_factorial] } },
  { refine [expr finset.sum_congr rfl (λ _ _, _)],
    simp [] [] ["only"] ["[", expr pow_add, ",", expr div_eq_inv_mul, ",", expr mul_inv₀, ",", expr mul_left_comm, ",", expr mul_assoc, "]"] [] [] },
  { rw ["[", "<-", expr mul_sum, "]"] [],
    apply [expr mul_le_mul_of_nonneg_left],
    { simp_rw ["[", "<-", expr div_pow, "]"] [],
      rw ["[", "<-", expr geom_sum_def, ",", expr geom_sum_eq, ",", expr div_le_iff_of_neg, "]"] [],
      { transitivity [expr («expr- »(1) : exprℝ())],
        { linarith [] [] [] },
        { simp [] [] ["only"] ["[", expr neg_le_sub_iff_le_add, ",", expr div_pow, ",", expr nat.cast_succ, ",", expr le_add_iff_nonneg_left, "]"] [] [],
          exact [expr div_nonneg (pow_nonneg (abs_nonneg x) k) (pow_nonneg «expr + »(n, 1).cast_nonneg k)] } },
      { linarith [] [] [] },
      { linarith [] [] [] } },
    { exact [expr div_nonneg (pow_nonneg (abs_nonneg x) n) (nat.cast_nonneg «expr !»(n))] } }
end

theorem abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1) ≤ 2*abs x :=
  calc abs (exp x - 1) = abs (exp x - ∑m in range 1, x ^ m / m !) :=
    by 
      simp [sum_range_succ]
    _ ≤ (abs x ^ 1)*Nat.succ 1*(1!*(1 : ℕ))⁻¹ :=
    exp_bound hx
      (by 
        decide)
    _ = 2*abs x :=
    by 
      simp [two_mul, mul_two, mul_addₓ, mul_commₓ]
    

theorem abs_exp_sub_one_sub_id_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1 - x) ≤ abs x ^ 2 :=
  calc abs (exp x - 1 - x) = abs (exp x - ∑m in range 2, x ^ m / m !) :=
    by 
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assocₓ]
    _ ≤ (abs x ^ 2)*Nat.succ 2*(2!*(2 : ℕ))⁻¹ :=
    exp_bound hx
      (by 
        decide)
    _ ≤ (abs x ^ 2)*1 :=
    mul_le_mul_of_nonneg_left
      (by 
        normNum)
      (sq_nonneg (abs x))
    _ = abs x ^ 2 :=
    by 
      rw [mul_oneₓ]
    

end Complex

namespace Real

open Complex Finset

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_bound
{x : exprℝ()}
(hx : «expr ≤ »(«expr| |»(x), 1))
{n : exprℕ()}
(hn : «expr < »(0, n)) : «expr ≤ »(«expr| |»(«expr - »(exp x, «expr∑ in , »((m), range n, «expr / »(«expr ^ »(x, m), «expr !»(m))))), «expr * »(«expr ^ »(«expr| |»(x), n), «expr / »(n.succ, «expr * »(«expr !»(n), n)))) :=
begin
  have [ident hxc] [":", expr «expr ≤ »(complex.abs x, 1)] [],
  by exact_mod_cast [expr hx],
  convert [] [expr exp_bound hxc hn] []; norm_cast []
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_bound'
{x : exprℝ()}
(h1 : «expr ≤ »(0, x))
(h2 : «expr ≤ »(x, 1))
{n : exprℕ()}
(hn : «expr < »(0, n)) : «expr ≤ »(real.exp x, «expr + »(«expr∑ in , »((m), finset.range n, «expr / »(«expr ^ »(x, m), «expr !»(m))), «expr / »(«expr * »(«expr ^ »(x, n), «expr + »(n, 1)), «expr * »(«expr !»(n), n)))) :=
begin
  have [ident h3] [":", expr «expr = »(«expr| |»(x), x)] [":=", expr by simpa [] [] [] [] [] []],
  have [ident h4] [":", expr «expr ≤ »(«expr| |»(x), 1)] [":=", expr by rwa [expr h3] []],
  have [ident h'] [] [":=", expr real.exp_bound h4 hn],
  rw [expr h3] ["at", ident h'],
  have [ident h''] [] [":=", expr (abs_sub_le_iff.1 h').1],
  have [ident t] [] [":=", expr sub_le_iff_le_add'.1 h''],
  simpa [] [] [] ["[", expr mul_div_assoc, "]"] [] ["using", expr t]
end

/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `exp_near_succ`), with `exp_near n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
def exp_near (n : ℕ) (x r : ℝ) : ℝ :=
  (∑m in range n, x ^ m / m !)+(x ^ n / n !)*r

@[simp]
theorem exp_near_zero x r : exp_near 0 x r = r :=
  by 
    simp [exp_near]

@[simp]
theorem exp_near_succ n x r : exp_near (n+1) x r = exp_near n x (1+(x / n+1)*r) :=
  by 
    simp [exp_near, range_succ, mul_addₓ, add_left_commₓ, add_assocₓ, pow_succₓ, div_eq_mul_inv, mul_inv₀] <;> acRfl

theorem exp_near_sub n x r₁ r₂ : exp_near n x r₁ - exp_near n x r₂ = (x ^ n / n !)*r₁ - r₂ :=
  by 
    simp [exp_near, mul_sub]

theorem exp_approx_end (n m : ℕ) (x : ℝ) (e₁ : (n+1) = m) (h : |x| ≤ 1) :
  |exp x - exp_near m x 0| ≤ (|x| ^ m / m !)*(m+1) / m :=
  by 
    simp [exp_near]
    convert exp_bound h _ using 1
    fieldSimp [mul_commₓ]
    linarith

theorem exp_approx_succ {n} {x a₁ b₁ : ℝ} (m : ℕ) (e₁ : (n+1) = m) (a₂ b₂ : ℝ)
  (e : |(1+(x / m)*a₂) - a₁| ≤ b₁ - (|x| / m)*b₂) (h : |exp x - exp_near m x a₂| ≤ (|x| ^ m / m !)*b₂) :
  |exp x - exp_near n x a₁| ≤ (|x| ^ n / n !)*b₁ :=
  by 
    refine' (_root_.abs_sub_le _ _ _).trans ((add_le_add_right h _).trans _)
    subst e₁ 
    rw [exp_near_succ, exp_near_sub, _root_.abs_mul]
    convert mul_le_mul_of_nonneg_left (le_sub_iff_add_le'.1 e) _
    ·
      simp [mul_addₓ, pow_succ'ₓ, div_eq_mul_inv, _root_.abs_mul, _root_.abs_inv, ←pow_abs, mul_inv₀]
      acRfl
    ·
      simp [_root_.div_nonneg, _root_.abs_nonneg]

theorem exp_approx_end' {n} {x a b : ℝ} (m : ℕ) (e₁ : (n+1) = m) (rm : ℝ) (er : «expr↑ » m = rm) (h : |x| ≤ 1)
  (e : |1 - a| ≤ b - (|x| / rm)*(rm+1) / rm) : |exp x - exp_near n x a| ≤ (|x| ^ n / n !)*b :=
  by 
    subst er <;>
      exact
        exp_approx_succ _ e₁ _ _
          (by 
            simpa using e)
          (exp_approx_end _ _ _ e₁ h)

theorem exp_1_approx_succ_eq {n} {a₁ b₁ : ℝ} {m : ℕ} (en : (n+1) = m) {rm : ℝ} (er : «expr↑ » m = rm)
  (h : |exp 1 - exp_near m 1 ((a₁ - 1)*rm)| ≤ (|1| ^ m / m !)*b₁*rm) : |exp 1 - exp_near n 1 a₁| ≤ (|1| ^ n / n !)*b₁ :=
  by 
    subst er 
    refine' exp_approx_succ _ en _ _ _ h 
    fieldSimp [show (m : ℝ) ≠ 0 by 
        normCast <;> linarith]

theorem exp_approx_start (x a b : ℝ) (h : |exp x - exp_near 0 x a| ≤ (|x| ^ 0 / 0!)*b) : |exp x - a| ≤ b :=
  by 
    simpa using h

theorem cos_bound {x : ℝ} (hx : |x| ≤ 1) : |cos x - (1 - x ^ 2 / 2)| ≤ (|x| ^ 4)*5 / 96 :=
  calc |cos x - (1 - x ^ 2 / 2)| = abs (Complex.cos x - (1 - x ^ 2 / 2)) :=
    by 
      rw [←abs_of_real] <;> simp [of_real_bit0, of_real_one, of_real_inv]
    _ = abs (((Complex.exp (x*I)+Complex.exp ((-x)*I)) - (2 - x ^ 2)) / 2) :=
    by 
      simp [Complex.cos, sub_div, add_div, neg_div, div_self (@two_ne_zero' ℂ _ _ _)]
    _ =
      abs
        (((Complex.exp (x*I) -
              ∑m in range 4, (x*I) ^ m / m !)+Complex.exp ((-x)*I) - ∑m in range 4, ((-x)*I) ^ m / m !) /
          2) :=
    congr_argₓ abs
      (congr_argₓ (fun x : ℂ => x / 2)
        (by 
          simp only [sum_range_succ]
          simp [pow_succₓ]
          apply Complex.ext <;> simp [div_eq_mul_inv, norm_sq] <;> ring))
    _ ≤
      abs
          ((Complex.exp (x*I) - ∑m in range 4, (x*I) ^ m / m !) /
            2)+abs ((Complex.exp ((-x)*I) - ∑m in range 4, ((-x)*I) ^ m / m !) / 2) :=
    by 
      rw [add_div] <;> exact abs_add _ _ 
    _ =
      (abs (Complex.exp (x*I) - ∑m in range 4, (x*I) ^ m / m !) /
          2)+abs (Complex.exp ((-x)*I) - ∑m in range 4, ((-x)*I) ^ m / m !) / 2 :=
    by 
      simp [Complex.abs_div]
    _ ≤
      (((Complex.abs (x*I) ^ 4)*Nat.succ 4*(4!*(4 : ℕ))⁻¹) /
          2)+((Complex.abs ((-x)*I) ^ 4)*Nat.succ 4*(4!*(4 : ℕ))⁻¹) / 2 :=
    add_le_add
      ((div_le_div_right
            (by 
              normNum)).2
        (Complex.exp_bound
          (by 
            simpa)
          (by 
            decide)))
      ((div_le_div_right
            (by 
              normNum)).2
        (Complex.exp_bound
          (by 
            simpa)
          (by 
            decide)))
    _ ≤ (|x| ^ 4)*5 / 96 :=
    by 
      normNum <;> simp [mul_assocₓ, mul_commₓ, mul_left_commₓ, mul_div_assoc]
    

theorem sin_bound {x : ℝ} (hx : |x| ≤ 1) : |sin x - (x - x ^ 3 / 6)| ≤ (|x| ^ 4)*5 / 96 :=
  calc |sin x - (x - x ^ 3 / 6)| = abs (Complex.sin x - (x - x ^ 3 / 6)) :=
    by 
      rw [←abs_of_real] <;> simp [of_real_bit0, of_real_one, of_real_inv]
    _ = abs ((((Complex.exp ((-x)*I) - Complex.exp (x*I))*I) - ((2*x) - x ^ 3 / 3)) / 2) :=
    by 
      simp [Complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left _ (@two_ne_zero' ℂ _ _ _), div_div_eq_div_mul,
        show ((3 : ℂ)*2) = 6by 
          normNum]
    _ =
      abs
        ((((Complex.exp ((-x)*I) - ∑m in range 4, ((-x)*I) ^ m / m !) -
              (Complex.exp (x*I) - ∑m in range 4, (x*I) ^ m / m !))*I) /
          2) :=
    congr_argₓ abs
      (congr_argₓ (fun x : ℂ => x / 2)
        (by 
          simp only [sum_range_succ]
          simp [pow_succₓ]
          apply Complex.ext <;> simp [div_eq_mul_inv, norm_sq] <;> ring))
    _ ≤
      abs
          (((Complex.exp ((-x)*I) - ∑m in range 4, ((-x)*I) ^ m / m !)*I) /
            2)+abs ((-(Complex.exp (x*I) - ∑m in range 4, (x*I) ^ m / m !)*I) / 2) :=
    by 
      rw [sub_mul, sub_eq_add_neg, add_div] <;> exact abs_add _ _ 
    _ =
      (abs (Complex.exp (x*I) - ∑m in range 4, (x*I) ^ m / m !) /
          2)+abs (Complex.exp ((-x)*I) - ∑m in range 4, ((-x)*I) ^ m / m !) / 2 :=
    by 
      simp [add_commₓ, Complex.abs_div, Complex.abs_mul]
    _ ≤
      (((Complex.abs (x*I) ^ 4)*Nat.succ 4*(4!*(4 : ℕ))⁻¹) /
          2)+((Complex.abs ((-x)*I) ^ 4)*Nat.succ 4*(4!*(4 : ℕ))⁻¹) / 2 :=
    add_le_add
      ((div_le_div_right
            (by 
              normNum)).2
        (Complex.exp_bound
          (by 
            simpa)
          (by 
            decide)))
      ((div_le_div_right
            (by 
              normNum)).2
        (Complex.exp_bound
          (by 
            simpa)
          (by 
            decide)))
    _ ≤ (|x| ^ 4)*5 / 96 :=
    by 
      normNum <;> simp [mul_assocₓ, mul_commₓ, mul_left_commₓ, mul_div_assoc]
    

theorem cos_pos_of_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < cos x :=
  calc 0 < 1 - x ^ 2 / 2 - (|x| ^ 4)*5 / 96 :=
    sub_pos.2$
      lt_sub_iff_add_lt.2
        (calc (((|x| ^ 4)*5 / 96)+x ^ 2 / 2) ≤ (1*5 / 96)+1 / 2 :=
          add_le_add
            (mul_le_mul_of_nonneg_right (pow_le_one _ (abs_nonneg _) hx)
              (by 
                normNum))
            ((div_le_div_right
                  (by 
                    normNum)).2
              (by 
                rw [sq, ←abs_mul_self, _root_.abs_mul] <;> exact mul_le_one hx (abs_nonneg _) hx))
          _ < 1 :=
          by 
            normNum
          )
    _ ≤ cos x := sub_le.1 (abs_sub_le_iff.1 (cos_bound hx)).2
    

theorem sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
  calc 0 < x - x ^ 3 / 6 - (|x| ^ 4)*5 / 96 :=
    sub_pos.2$
      lt_sub_iff_add_lt.2
        (calc (((|x| ^ 4)*5 / 96)+x ^ 3 / 6) ≤ (x*5 / 96)+x / 6 :=
          add_le_add
            (mul_le_mul_of_nonneg_right
              (calc |x| ^ 4 ≤ |x| ^ 1 :=
                pow_le_pow_of_le_one (abs_nonneg _)
                  (by 
                    rwa [_root_.abs_of_nonneg (le_of_ltₓ hx0)])
                  (by 
                    decide)
                _ = x :=
                by 
                  simp [_root_.abs_of_nonneg (le_of_ltₓ hx0)]
                )
              (by 
                normNum))
            ((div_le_div_right
                  (by 
                    normNum)).2
              (calc x ^ 3 ≤ x ^ 1 :=
                pow_le_pow_of_le_one (le_of_ltₓ hx0) hx
                  (by 
                    decide)
                _ = x := pow_oneₓ _
                ))
          _ < x :=
          by 
            linarith
          )
    _ ≤ sin x :=
    sub_le.1
      (abs_sub_le_iff.1
          (sin_bound
            (by 
              rwa [_root_.abs_of_nonneg (le_of_ltₓ hx0)]))).2
    

theorem sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
  have  : x / 2 ≤ 1 :=
    (div_le_iff
          (by 
            normNum)).mpr
      (by 
        simpa)
  calc 0 < (2*sin (x / 2))*cos (x / 2) :=
    mul_pos
      (mul_pos
        (by 
          normNum)
        (sin_pos_of_pos_of_le_one (half_pos hx0) this))
      (cos_pos_of_le_one
        (by 
          rwa [_root_.abs_of_nonneg (le_of_ltₓ (half_pos hx0))]))
    _ = sin x :=
    by 
      rw [←sin_two_mul, two_mul, add_halves]
    

theorem cos_one_le : cos 1 ≤ 2 / 3 :=
  calc cos 1 ≤ ((|(1 : ℝ)| ^ 4)*5 / 96)+1 - 1 ^ 2 / 2 :=
    sub_le_iff_le_add.1
      (abs_sub_le_iff.1
          (cos_bound
            (by 
              simp ))).1
    _ ≤ 2 / 3 :=
    by 
      normNum
    

theorem cos_one_pos : 0 < cos 1 :=
  cos_pos_of_le_one (le_of_eqₓ abs_one)

theorem cos_two_neg : cos 2 < 0 :=
  calc cos 2 = cos (2*1) := congr_argₓ cos (mul_oneₓ _).symm 
    _ = _ := Real.cos_two_mul 1
    _ ≤ (2*(2 / 3) ^ 2) - 1 :=
    sub_le_sub_right
      (mul_le_mul_of_nonneg_left
        (by 
          rw [sq, sq]
          exact mul_self_le_mul_self (le_of_ltₓ cos_one_pos) cos_one_le)
        zero_le_two)
      _ 
    _ < 0 :=
    by 
      normNum
    

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_bound_div_one_sub_of_interval_approx
{x : exprℝ()}
(h1 : «expr ≤ »(0, x))
(h2 : «expr ≤ »(x, 1)) : «expr ≤ »(«expr + »(«expr∑ in , »((j : exprℕ()), finset.range 3, «expr / »(«expr ^ »(x, j), j.factorial)), «expr / »(«expr * »(«expr ^ »(x, 3), «expr + »((3 : exprℕ()), 1)), «expr * »((3 : exprℕ()).factorial, (3 : exprℕ())))), «expr∑ in , »((j), finset.range 3, «expr ^ »(x, j))) :=
begin
  norm_num ["[", expr finset.sum, "]"] [],
  rw ["[", expr add_assoc, ",", expr add_comm «expr + »(x, 1) «expr / »(«expr * »(«expr ^ »(x, 3), 4), 18), ",", "<-", expr add_assoc, ",", expr add_le_add_iff_right, ",", "<-", expr add_le_add_iff_left «expr- »(«expr / »(«expr ^ »(x, 2), 2)), ",", "<-", expr add_assoc, ",", expr comm_ring.add_left_neg «expr / »(«expr ^ »(x, 2), 2), ",", expr zero_add, ",", expr neg_add_eq_sub, ",", expr sub_half, ",", expr sq, ",", expr pow_succ, ",", expr sq, "]"] [],
  have [ident i1] [":", expr «expr ≤ »(«expr / »(«expr * »(x, 4), 18), «expr / »(1, 2))] [":=", expr by linarith [] [] []],
  have [ident i2] [":", expr «expr ≤ »(0, «expr / »(«expr * »(x, 4), 18))] [":=", expr by linarith [] [] []],
  have [ident i3] [] [":=", expr mul_le_mul h1 h1 le_rfl h1],
  rw [expr zero_mul] ["at", ident i3],
  have [ident t] [] [":=", expr mul_le_mul le_rfl i1 i2 i3],
  rw ["<-", expr mul_assoc] [],
  rwa ["[", expr mul_one_div, ",", "<-", expr mul_div_assoc, ",", "<-", expr mul_assoc, "]"] ["at", ident t]
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exp_bound_div_one_sub_of_interval
{x : exprℝ()}
(h1 : «expr ≤ »(0, x))
(h2 : «expr < »(x, 1)) : «expr ≤ »(real.exp x, «expr / »(1, «expr - »(1, x))) :=
begin
  have [ident h] [":", expr «expr ≤ »(«expr∑ in , »((j), finset.range 3, «expr ^ »(x, j)), «expr / »(1, «expr - »(1, x)))] [],
  { norm_num ["[", expr finset.sum, "]"] [],
    have [ident h1x] [":", expr «expr < »(0, «expr - »(1, x))] [":=", expr by simpa [] [] [] [] [] []],
    rw [expr le_div_iff h1x] [],
    norm_num ["[", "<-", expr add_assoc, ",", expr mul_sub_left_distrib, ",", expr mul_one, ",", expr add_mul, ",", expr sub_add_eq_sub_sub, ",", expr pow_succ' x 2, "]"] [],
    have [ident hx3] [":", expr «expr ≤ »(0, «expr ^ »(x, 3))] [],
    { norm_num [] [],
      exact [expr h1] },
    linarith [] [] [] },
  exact [expr «expr $ »(exp_bound' h1 h2.le, by linarith [] [] []).trans ((exp_bound_div_one_sub_of_interval_approx h1 h2.le).trans h)]
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem one_sub_le_exp_minus_of_pos
{y : exprℝ()}
(h : «expr ≤ »(0, y)) : «expr ≤ »(«expr - »(1, y), real.exp «expr- »(y)) :=
begin
  rw [expr real.exp_neg] [],
  have [ident r1] [":", expr «expr ≤ »(«expr * »(«expr - »(1, y), real.exp y), 1)] [],
  { cases [expr le_or_lt «expr - »(1, y) 0] [],
    { have [ident h''] [":", expr «expr ≤ »(«expr * »(«expr - »(1, y), y.exp), 0)] [],
      { rw [expr mul_nonpos_iff] [],
        right,
        exact [expr ⟨h_1, y.exp_pos.le⟩] },
      linarith [] [] [] },
    have [ident hy1] [":", expr «expr < »(y, 1)] [":=", expr by linarith [] [] []],
    rw ["<-", expr le_div_iff' h_1] [],
    exact [expr exp_bound_div_one_sub_of_interval h hy1] },
  rw [expr inv_eq_one_div] [],
  rw [expr le_div_iff' y.exp_pos] [],
  rwa [expr mul_comm] ["at", ident r1]
end

-- error in Data.Complex.Exponential: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_one_le_exp_of_nonpos {x : exprℝ()} (h : «expr ≤ »(x, 0)) : «expr ≤ »(«expr + »(x, 1), real.exp x) :=
begin
  rw [expr add_comm] [],
  have [ident h1] [":", expr «expr ≤ »(0, «expr- »(x))] [":=", expr by linarith [] [] []],
  simpa [] [] [] [] [] ["using", expr one_sub_le_exp_minus_of_pos h1]
end

theorem add_one_le_exp (x : ℝ) : (x+1) ≤ Real.exp x :=
  by 
    cases le_or_ltₓ 0 x
    ·
      exact Real.add_one_le_exp_of_nonneg h 
    exact add_one_le_exp_of_nonpos h.le

end Real

namespace Complex

@[simp]
theorem abs_cos_add_sin_mul_I (x : ℝ) : abs (cos x+sin x*I) = 1 :=
  have  := Real.sin_sq_add_cos_sq x 
  by 
    simp_all [add_commₓ, abs, norm_sq, sq, sin_of_real_re, cos_of_real_re, mul_re]

@[simp]
theorem abs_exp_of_real (x : ℝ) : abs (exp x) = Real.exp x :=
  by 
    rw [←of_real_exp] <;> exact abs_of_nonneg (le_of_ltₓ (Real.exp_pos _))

@[simp]
theorem abs_exp_of_real_mul_I (x : ℝ) : abs (exp (x*I)) = 1 :=
  by 
    rw [exp_mul_I, abs_cos_add_sin_mul_I]

theorem abs_exp (z : ℂ) : abs (exp z) = Real.exp z.re :=
  by 
    rw [exp_eq_exp_re_mul_sin_add_cos, abs_mul, abs_exp_of_real, abs_cos_add_sin_mul_I, mul_oneₓ]

theorem abs_exp_eq_iff_re_eq {x y : ℂ} : abs (exp x) = abs (exp y) ↔ x.re = y.re :=
  by 
    rw [abs_exp, abs_exp, Real.exp_eq_exp]

end Complex

