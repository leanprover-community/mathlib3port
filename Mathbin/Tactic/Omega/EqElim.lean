import Mathbin.Tactic.Omega.Clause

open List.Func

namespace Omega

def symdiv (i j : Int) : Int :=
  if (2*i % j) < j then i / j else (i / j)+1

def symmod (i j : Int) : Int :=
  if (2*i % j) < j then i % j else i % j - j

attribute [local semireducible] Int.Nonneg

theorem symmod_add_one_self {i : Int} : 0 < i → symmod i (i+1) = -1 :=
  by 
    intro h1 
    unfold symmod 
    rw [Int.mod_eq_of_lt (le_of_ltₓ h1) (lt_add_one _), if_neg]
    simp only [add_commₓ, add_neg_cancel_left, neg_add_rev, sub_eq_add_neg]
    have h2 : (2*i) = (1+1)*i := rfl 
    simpa only [h2, add_mulₓ, one_mulₓ, add_lt_add_iff_left, not_ltₓ] using h1

-- error in Tactic.Omega.EqElim: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem mul_symdiv_eq {i j : int} : «expr = »(«expr * »(j, symdiv i j), «expr - »(i, symmod i j)) :=
begin
  unfold [ident symdiv] [],
  unfold [ident symmod] [],
  by_cases [expr h1, ":", expr «expr < »(«expr * »(2, «expr % »(i, j)), j)],
  { repeat { rw [expr if_pos h1] [] },
    rw ["[", expr int.mod_def, ",", expr sub_sub_cancel, "]"] [] },
  { repeat { rw [expr if_neg h1] [] },
    rw ["[", expr int.mod_def, ",", expr sub_sub, ",", expr sub_sub_cancel, ",", expr mul_add, ",", expr mul_one, "]"] [] }
end

theorem symmod_eq {i j : Int} : symmod i j = i - j*symdiv i j :=
  by 
    rw [mul_symdiv_eq, sub_sub_cancel]

/-- (sgm v b as n) is the new value assigned to the nth variable
after a single step of equality elimination using valuation v,
term ⟨b, as⟩, and variable index n. If v satisfies the initial
constraint set, then (v ⟨n ↦ sgm v b as n⟩) satisfies the new
constraint set after equality elimination. -/
def sgm (v : Nat → Int) (b : Int) (as : List Int) (n : Nat) :=
  let a_n : Int := get n as 
  let m : Int := a_n+1
  (symmod b m+coeffs.val v (as.map fun x => symmod x m)) / m

open_locale List.Func

def rhs : Nat → Int → List Int → term
| n, b, as =>
  let m := get n as+1
  ⟨symmod b m, (as.map fun x => symmod x m) {n ↦ -m}⟩

-- error in Tactic.Omega.EqElim: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem rhs_correct_aux
{v : nat → int}
{m : int}
{as : list int} : ∀
{k}, «expr∃ , »((d), «expr = »(«expr + »(«expr * »(m, d), coeffs.val_between v (as.map (λ
     x : exprℤ(), symmod x m)) 0 k), coeffs.val_between v as 0 k))
| 0 := begin
  existsi [expr (0 : int)],
  simp [] [] ["only"] ["[", expr add_zero, ",", expr mul_zero, ",", expr coeffs.val_between, "]"] [] []
end
| «expr + »(k, 1) := begin
  simp [] [] ["only"] ["[", expr zero_add, ",", expr coeffs.val_between, ",", expr list.map, "]"] [] [],
  cases [expr @rhs_correct_aux k] ["with", ident d, ident h1],
  rw ["<-", expr h1] [],
  by_cases [expr hk, ":", expr «expr < »(k, as.length)],
  { rw ["[", expr get_map hk, ",", expr symmod_eq, ",", expr sub_mul, "]"] [],
    existsi [expr «expr + »(d, «expr * »(symdiv (get k as) m, v k))],
    ring [] },
  { rw [expr not_lt] ["at", ident hk],
    repeat { rw [expr get_eq_default_of_le] [] },
    existsi [expr d],
    rw [expr add_assoc] [],
    exact [expr hk],
    simp [] [] ["only"] ["[", expr hk, ",", expr list.length_map, "]"] [] [] }
end

open_locale Omega

-- error in Tactic.Omega.EqElim: ././Mathport/Syntax/Translate/Basic.lean:340:40: in apply: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem rhs_correct
{v : nat → int}
{b : int}
{as : list int}
(n : nat) : «expr < »(0, get n as) → «expr = »(0, term.val v (b, as)) → «expr = »(v n, term.val «expr ⟨ ↦ ⟩»(v, n, sgm v b as n) (rhs n b as)) :=
begin
  intros [ident h0, ident h1],
  let [ident a_n] [] [":=", expr get n as],
  let [ident m] [] [":=", expr «expr + »(a_n, 1)],
  have [ident h3] [":", expr «expr ≠ »(m, 0)] [],
  { apply [expr ne_of_gt],
    apply [expr lt_trans h0],
    simp [] [] [] ["[", expr a_n, ",", expr m, "]"] [] [] },
  have [ident h2] [":", expr «expr = »(«expr * »(m, sgm v b as n), «expr + »(symmod b m, coeffs.val v (as.map (λ
       x, symmod x m))))] [],
  { simp [] [] ["only"] ["[", expr sgm, ",", expr mul_comm m, "]"] [] [],
    rw ["[", expr int.div_mul_cancel, "]"] [],
    have [ident h4] [":", expr «expr∃ , »((c), «expr = »(«expr + »(«expr * »(m, c), «expr + »(symmod b «expr + »(get n as, 1), coeffs.val v (as.map (λ
           x : exprℤ(), symmod x m)))), term.val v (b, as)))] [],
    { have [ident h5] [":", expr «expr∃ , »((d), «expr = »(«expr + »(«expr * »(m, d), coeffs.val v (as.map (λ
            x, symmod x m))), coeffs.val v as))] [],
      { simp [] [] ["only"] ["[", expr coeffs.val, ",", expr list.length_map, "]"] [] [],
        apply [expr rhs_correct_aux] },
      cases [expr h5] ["with", ident d, ident h5],
      rw [expr symmod_eq] [],
      existsi [expr «expr + »(symdiv b m, d)],
      unfold [ident term.val] [],
      rw ["<-", expr h5] [],
      simp [] [] ["only"] ["[", expr term.val, ",", expr mul_add, ",", expr add_mul, ",", expr m, ",", expr a_n, "]"] [] [],
      ring [] },
    cases [expr h4] ["with", ident c, ident h4],
    rw ["[", expr dvd_add_iff_right (dvd_mul_right m c), ",", expr h4, ",", "<-", expr h1, "]"] [],
    apply [expr dvd_zero] },
  apply [expr calc
     «expr = »(v n, «expr + »(«expr + »(«expr- »(«expr * »(m, sgm v b as n)), symmod b m), coeffs.val_except n v (as.map (λ
         x, symmod x m)))) : begin
       rw ["[", expr h2, ",", "<-", expr coeffs.val_except_add_eq n, "]"] [],
       have [ident hn] [":", expr «expr < »(n, as.length)] [],
       { by_contra [ident hc],
         rw [expr not_lt] ["at", ident hc],
         rw [expr get_eq_default_of_le n hc] ["at", ident h0],
         cases [expr h0] [] },
       rw [expr get_map hn] [],
       simp [] [] ["only"] ["[", expr a_n, ",", expr m, "]"] [] [],
       rw ["[", expr add_comm, ",", expr symmod_add_one_self h0, "]"] [],
       ring []
     end
     «expr = »(..., term.val «expr ⟨ ↦ ⟩»(v, n, sgm v b as n) (rhs n b as)) : begin
       unfold [ident rhs] [],
       unfold [ident term.val] [],
       rw ["[", "<-", expr coeffs.val_except_add_eq n, ",", expr get_set, ",", expr update_eq, "]"] [],
       have [ident h2] [":", expr ∀
        a
        b
        c : int, «expr = »(«expr + »(«expr + »(a, b), c), «expr + »(b, «expr + »(c, a)))] [":=", expr by { intros [],
          ring [] }],
       rw [expr h2 «expr- »(_)] [],
       apply [expr fun_mono_2 rfl],
       apply [expr fun_mono_2],
       { rw [expr coeffs.val_except_update_set] [] },
       { simp [] [] ["only"] ["[", expr m, ",", expr a_n, "]"] [] [],
         ring [] }
     end]
end

def sym_sym (m b : Int) : Int :=
  symdiv b m+symmod b m

def coeffs_reduce : Nat → Int → List Int → term
| n, b, as =>
  let a := get n as 
  let m := a+1
  (sym_sym m b, as.map (sym_sym m) {n ↦ -a})

-- error in Tactic.Omega.EqElim: ././Mathport/Syntax/Translate/Basic.lean:340:40: in have: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem coeffs_reduce_correct
{v : nat → int}
{b : int}
{as : list int}
{n : nat} : «expr < »(0, get n as) → «expr = »(0, term.val v (b, as)) → «expr = »(0, term.val «expr ⟨ ↦ ⟩»(v, n, sgm v b as n) (coeffs_reduce n b as)) :=
begin
  intros [ident h1, ident h2],
  let [ident a_n] [] [":=", expr get n as],
  let [ident m] [] [":=", expr «expr + »(a_n, 1)],
  have [ident h3] [":", expr «expr ≠ »(m, 0)] [],
  { apply [expr ne_of_gt],
    apply [expr lt_trans h1],
    simp [] [] ["only"] ["[", expr m, ",", expr lt_add_iff_pos_right, "]"] [] [] },
  have [ident h4] [":", expr «expr = »(0, «expr * »(term.val «expr ⟨ ↦ ⟩»(v, n, sgm v b as n) (coeffs_reduce n b as), m))] [":=", expr calc
     «expr = »(0, term.val v (b, as)) : h2
     «expr = »(..., «expr + »(«expr + »(b, coeffs.val_except n v as), «expr * »(a_n, (rhs n b as).val «expr ⟨ ↦ ⟩»(v, n, sgm v b as n)))) : begin
       unfold [ident term.val] [],
       rw ["[", "<-", expr coeffs.val_except_add_eq n, ",", expr rhs_correct n h1 h2, "]"] [],
       simp [] [] ["only"] ["[", expr a_n, ",", expr add_assoc, "]"] [] []
     end
     «expr = »(..., «expr + »(«expr + »(«expr- »(«expr * »(«expr * »(m, a_n), sgm v b as n)), «expr + »(b, «expr * »(a_n, symmod b m))), «expr + »(coeffs.val_except n v as, «expr * »(a_n, coeffs.val_except n v (as.map (λ
           x, symmod x m)))))) : begin
       simp [] [] ["only"] ["[", expr term.val, ",", expr rhs, ",", expr mul_add, ",", expr m, ",", expr a_n, ",", expr add_assoc, ",", expr add_right_inj, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [],
       rw ["[", "<-", expr coeffs.val_except_add_eq n, ",", expr get_set, ",", expr update_eq, ",", expr mul_add, "]"] [],
       apply [expr fun_mono_2],
       { rw [expr coeffs.val_except_eq_val_except update_eq_of_ne (get_set_eq_of_ne _)] [] },
       simp [] [] ["only"] ["[", expr m, "]"] [] [],
       ring []
     end
     «expr = »(..., «expr + »(«expr + »(«expr- »(«expr * »(«expr * »(m, a_n), sgm v b as n)), «expr + »(b, «expr * »(a_n, symmod b m))), coeffs.val_except n v (as.map (λ
         a_i, «expr + »(a_i, «expr * »(a_n, symmod a_i m)))))) : begin
       apply [expr fun_mono_2 rfl],
       simp [] [] ["only"] ["[", expr coeffs.val_except, ",", expr mul_add, "]"] [] [],
       repeat { rw ["<-", expr coeffs.val_between_map_mul] [] },
       have [ident h4] [":", expr ∀
        {a
         b
         c
         d : int}, «expr = »(«expr + »(«expr + »(a, b), «expr + »(c, d)), «expr + »(«expr + »(a, c), «expr + »(b, d)))] [],
       { intros [],
         ring [] },
       rw [expr h4] [],
       have [ident h5] [":", expr «expr = »(add as (list.map (has_mul.mul a_n) (list.map (λ
            x : exprℤ(), symmod x «expr + »(get n as, 1)) as)), list.map (λ
          a_i : exprℤ(), «expr + »(a_i, «expr * »(a_n, symmod a_i m))) as)] [],
       { rw ["[", expr list.map_map, ",", "<-", expr map_add_map, "]"] [],
         apply [expr fun_mono_2],
         { have [ident h5] [":", expr «expr = »(λ x : int, x, id)] [],
           { rw [expr function.funext_iff] [],
             intro [ident x],
             refl },
           rw ["[", expr h5, ",", expr list.map_id, "]"] [] },
         { apply [expr fun_mono_2 _ rfl],
           rw [expr function.funext_iff] [],
           intro [ident x],
           simp [] [] ["only"] ["[", expr m, "]"] [] [] } },
       simp [] [] ["only"] ["[", expr list.length_map, "]"] [] [],
       repeat { rw ["[", "<-", expr coeffs.val_between_add, ",", expr h5, "]"] [] }
     end
     «expr = »(..., «expr + »(«expr + »(«expr- »(«expr * »(«expr * »(m, a_n), sgm v b as n)), «expr * »(m, sym_sym m b)), coeffs.val_except n v (as.map (λ
         a_i, «expr * »(m, sym_sym m a_i))))) : begin
       repeat { rw [expr add_assoc] [] },
       apply [expr fun_mono_2],
       refl,
       rw ["<-", expr add_assoc] [],
       have [ident h4] [":", expr ∀
        x : exprℤ(), «expr = »(«expr + »(x, «expr * »(a_n, symmod x m)), «expr * »(m, sym_sym m x))] [],
       { intro [ident x],
         have [ident h5] [":", expr «expr = »(a_n, «expr - »(m, 1))] [],
         { simp [] [] ["only"] ["[", expr m, "]"] [] [],
           rw [expr add_sub_cancel] [] },
         rw ["[", expr h5, ",", expr sub_mul, ",", expr one_mul, ",", expr add_sub, ",", expr add_comm, ",", expr add_sub_assoc, ",", "<-", expr mul_symdiv_eq, "]"] [],
         simp [] [] ["only"] ["[", expr sym_sym, ",", expr mul_add, ",", expr add_comm, "]"] [] [] },
       apply [expr fun_mono_2 (h4 _)],
       apply [expr coeffs.val_except_eq_val_except]; intros [ident x, ident h5],
       refl,
       apply [expr congr_arg],
       apply [expr fun_mono_2 _ rfl],
       rw [expr function.funext_iff] [],
       apply [expr h4]
     end
     «expr = »(..., «expr * »(«expr + »(«expr + »(«expr- »(«expr * »(a_n, sgm v b as n)), sym_sym m b), coeffs.val_except n v (as.map (sym_sym m))), m)) : begin
       simp [] [] ["only"] ["[", expr add_mul _ _ m, "]"] [] [],
       apply [expr fun_mono_2],
       ring [],
       simp [] [] ["only"] ["[", expr coeffs.val_except, ",", expr add_mul _ _ m, "]"] [] [],
       apply [expr fun_mono_2],
       { rw ["[", expr mul_comm _ m, ",", "<-", expr coeffs.val_between_map_mul, ",", expr list.map_map, "]"] [] },
       simp [] [] ["only"] ["[", expr list.length_map, ",", expr mul_comm _ m, "]"] [] [],
       rw ["[", "<-", expr coeffs.val_between_map_mul, ",", expr list.map_map, "]"] []
     end
     «expr = »(..., «expr * »(«expr + »(sym_sym m b, «expr + »(coeffs.val_except n v (as.map (sym_sym m)), «expr * »(«expr- »(a_n), sgm v b as n))), m)) : by ring []
     «expr = »(..., «expr * »(term.val «expr ⟨ ↦ ⟩»(v, n, sgm v b as n) (coeffs_reduce n b as), m)) : begin
       simp [] [] ["only"] ["[", expr coeffs_reduce, ",", expr term.val, ",", expr m, ",", expr a_n, "]"] [] [],
       rw ["[", "<-", expr coeffs.val_except_add_eq n, ",", expr coeffs.val_except_update_set, ",", expr get_set, ",", expr update_eq, "]"] []
     end],
  rw ["[", "<-", expr int.mul_div_cancel (term.val _ _) h3, ",", "<-", expr h4, ",", expr int.zero_div, "]"] []
end

def cancel (m : Nat) (t1 t2 : term) : term :=
  term.add (t1.mul (-get m t2.snd)) t2

def subst (n : Nat) (t1 t2 : term) : term :=
  term.add (t1.mul (get n t2.snd)) (t2.fst, t2.snd {n ↦ 0})

theorem subst_correct {v : Nat → Int} {b : Int} {as : List Int} {t : term} {n : Nat} :
  0 < get n as → 0 = term.val v (b, as) → term.val v t = term.val (v ⟨n ↦ sgm v b as n⟩) (subst n (rhs n b as) t) :=
  by 
    intro h1 h2 
    simp only [subst, term.val, term.val_add, term.val_mul]
    rw [←rhs_correct _ h1 h2]
    cases' t with b' as' 
    simp only [term.val]
    have h3 : coeffs.val (v ⟨n ↦ sgm v b as n⟩) (as' {n ↦ 0}) = coeffs.val_except n v as'
    ·
      rw [←coeffs.val_except_add_eq n, get_set, zero_mul, add_zeroₓ, coeffs.val_except_update_set]
    rw [h3, ←coeffs.val_except_add_eq n]
    ring

-- error in Tactic.Omega.EqElim: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler has_reflect
/-- The type of equality elimination rules. -/
@[derive #[expr has_reflect], derive #[expr inhabited]]
inductive ee : Type
| drop : ee
| nondiv : int → ee
| factor : int → ee
| neg : ee
| reduce : nat → ee
| cancel : nat → ee

namespace Ee

def reprₓ : ee → Stringₓ
| drop => "↓"
| nondiv i => i.repr ++ "∤"
| factor i => "/" ++ i.repr
| neg => "-"
| reduce n => "≻" ++ n.repr
| cancel n => "+" ++ n.repr

instance HasRepr : HasRepr ee :=
  ⟨reprₓ⟩

unsafe instance has_to_format : has_to_format ee :=
  ⟨fun x => x.repr⟩

end Ee

/-- Apply a given sequence of equality elimination steps to a clause. -/
def eq_elim : List ee → clause → clause
| [], ([], les) => ([], les)
| [], (_ :: _, les) => ([], [])
| _ :: _, ([], les) => ([], [])
| ee.drop :: es, (Eq :: eqs, les) => eq_elim es (eqs, les)
| ee.neg :: es, (Eq :: eqs, les) => eq_elim es (eq.neg :: eqs, les)
| ee.nondiv i :: es, ((b, as) :: eqs, les) => if ¬i ∣ b ∧ ∀ x _ : x ∈ as, i ∣ x then ([], [⟨-1, []⟩]) else ([], [])
| ee.factor i :: es, ((b, as) :: eqs, les) =>
  if i ∣ b ∧ ∀ x _ : x ∈ as, i ∣ x then eq_elim es (term.div i (b, as) :: eqs, les) else ([], [])
| ee.reduce n :: es, ((b, as) :: eqs, les) =>
  if 0 < get n as then
    let eq' := coeffs_reduce n b as 
    let r := rhs n b as 
    let eqs' := eqs.map (subst n r)
    let les' := les.map (subst n r)
    eq_elim es (eq' :: eqs', les')
  else ([], [])
| ee.cancel m :: es, (Eq :: eqs, les) => eq_elim es (eqs.map (cancel m Eq), les.map (cancel m Eq))

open Tactic

theorem sat_empty : clause.sat ([], []) :=
  ⟨fun _ => 0,
    ⟨by 
        decide,
      by 
        decide⟩⟩

theorem sat_eq_elim : ∀ {es : List ee} {c : clause}, c.sat → (eq_elim es c).sat
| [], ([], les), h => h
| e :: _, ([], les), h =>
  by 
    cases e <;> simp only [eq_elim] <;> apply sat_empty
| [], (_ :: _, les), h => sat_empty
| ee.drop :: es, (Eq :: eqs, les), h1 =>
  by 
    apply @sat_eq_elim es _ _ 
    rcases h1 with ⟨v, h1, h2⟩
    refine' ⟨v, List.forall_mem_of_forall_mem_consₓ h1, h2⟩
| ee.neg :: es, (Eq :: eqs, les), h1 =>
  by 
    simp only [eq_elim]
    apply sat_eq_elim 
    cases' h1 with v h1 
    exists v 
    cases' h1 with hl hr 
    apply And.intro _ hr 
    rw [List.forall_mem_consₓ] at *
    apply And.intro _ hl.right 
    rw [term.val_neg]
    rw [←hl.left]
    rfl
| ee.nondiv i :: es, ((b, as) :: eqs, les), h1 =>
  by 
    unfold eq_elim 
    byCases' h2 : ¬i ∣ b ∧ ∀ x : ℤ, x ∈ as → i ∣ x
    ·
      exFalso 
      cases' h1 with v h1 
      have h3 : 0 = b+coeffs.val v as := h1.left _ (Or.inl rfl)
      have h4 : i ∣ coeffs.val v as := coeffs.dvd_val h2.right 
      have h5 : i ∣ b+coeffs.val v as :=
        by 
          rw [←h3]
          apply dvd_zero 
      rw [←dvd_add_iff_left h4] at h5 
      apply h2.left h5 
    rw [if_neg h2]
    apply sat_empty
| ee.factor i :: es, ((b, as) :: eqs, les), h1 =>
  by 
    simp only [eq_elim]
    byCases' h2 : i ∣ b ∧ ∀ x _ : x ∈ as, i ∣ x
    ·
      rw [if_pos h2]
      apply sat_eq_elim 
      cases' h1 with v h1 
      exists v 
      cases' h1 with h3 h4 
      apply And.intro _ h4 
      rw [List.forall_mem_consₓ] at *
      cases' h3 with h5 h6 
      apply And.intro _ h6 
      rw [term.val_div h2.left h2.right, ←h5, Int.zero_div]
    ·
      rw [if_neg h2]
      apply sat_empty
| ee.reduce n :: es, ((b, as) :: eqs, les), h1 =>
  by 
    simp only [eq_elim]
    byCases' h2 : 0 < get n as 
    runTac 
      tactic.rotate 1
    ·
      rw [if_neg h2]
      apply sat_empty 
    rw [if_pos h2]
    apply sat_eq_elim 
    cases' h1 with v h1 
    exists v ⟨n ↦ sgm v b as n⟩
    cases' h1 with h1 h3 
    rw [List.forall_mem_consₓ] at h1 
    cases' h1 with h4 h5 
    constructor
    ·
      rw [List.forall_mem_consₓ]
      constructor
      ·
        apply coeffs_reduce_correct h2 h4
      ·
        intro x h6 
        rw [List.mem_mapₓ] at h6 
        cases' h6 with t h6 
        cases' h6 with h6 h7 
        rw [←h7, ←subst_correct h2 h4]
        apply h5 _ h6
    ·
      intro x h6 
      rw [List.mem_mapₓ] at h6 
      cases' h6 with t h6 
      cases' h6 with h6 h7 
      rw [←h7, ←subst_correct h2 h4]
      apply h3 _ h6
| ee.cancel m :: es, (Eq :: eqs, les), h1 =>
  by 
    unfold eq_elim 
    apply sat_eq_elim 
    cases' h1 with v h1 
    exists v 
    cases' h1 with h1 h2 
    rw [List.forall_mem_consₓ] at h1 
    cases' h1 with h1 h3 
    constructor <;>
      intro t h4 <;>
        rw [List.mem_mapₓ] at h4 <;>
          rcases h4 with ⟨s, h4, h5⟩ <;>
            rw [←h5] <;> simp only [term.val_add, term.val_mul, cancel] <;> rw [←h1, mul_zero, zero_addₓ]
    ·
      apply h3 _ h4
    ·
      apply h2 _ h4

/-- If the result of equality elimination is unsatisfiable, the original clause is unsatisfiable. -/
theorem unsat_of_unsat_eq_elim (ee : List ee) (c : clause) : (eq_elim ee c).Unsat → c.unsat :=
  by 
    intro h1 h2 
    apply h1 
    apply sat_eq_elim h2

end Omega

