import Mathbin.Computability.PartrecCode

/-!
# Computability theory and the halting problem

A universal partial recursive function, Rice's theorem, and the halting problem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/


open Encodable Denumerable

namespace Nat.Partrec

open Computable Part

-- error in Computability.Halting: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem merge'
{f g}
(hf : nat.partrec f)
(hg : nat.partrec g) : «expr∃ , »((h), «expr ∧ »(nat.partrec h, ∀
  a, «expr ∧ »(∀
   x «expr ∈ » h a, «expr ∨ »(«expr ∈ »(x, f a), «expr ∈ »(x, g a)), «expr ↔ »((h a).dom, «expr ∨ »((f a).dom, (g a).dom))))) :=
begin
  obtain ["⟨", ident cf, ",", ident rfl, "⟩", ":=", expr code.exists_code.1 hf],
  obtain ["⟨", ident cg, ",", ident rfl, "⟩", ":=", expr code.exists_code.1 hg],
  have [] [":", expr nat.partrec (λ
    n, nat.rfind_opt (λ
     k, «expr <|> »(cf.evaln k n, cg.evaln k n)))] [":=", expr partrec.nat_iff.1 «expr $ »(partrec.rfind_opt, primrec.option_orelse.to_comp.comp «expr $ »(code.evaln_prim.to_comp.comp, (snd.pair (const cf)).pair fst) «expr $ »(code.evaln_prim.to_comp.comp, (snd.pair (const cg)).pair fst))],
  refine [expr ⟨_, this, λ n, _⟩],
  suffices [] [],
  refine [expr ⟨this, ⟨λ h, (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, _⟩⟩],
  { intro [ident h],
    rw [expr nat.rfind_opt_dom] [],
    simp [] [] ["only"] ["[", expr dom_iff_mem, ",", expr code.evaln_complete, ",", expr option.mem_def, "]"] [] ["at", ident h],
    obtain ["⟨", ident x, ",", ident k, ",", ident e, "⟩", "|", "⟨", ident x, ",", ident k, ",", ident e, "⟩", ":=", expr h],
    { refine [expr ⟨k, x, _⟩],
      simp [] [] ["only"] ["[", expr e, ",", expr option.some_orelse, ",", expr option.mem_def, "]"] [] [] },
    { refine [expr ⟨k, _⟩],
      cases [expr cf.evaln k n] ["with", ident y],
      { exact [expr ⟨x, by simp [] [] ["only"] ["[", expr e, ",", expr option.mem_def, ",", expr option.none_orelse, "]"] [] []⟩] },
      { exact [expr ⟨y, by simp [] [] ["only"] ["[", expr option.some_orelse, ",", expr option.mem_def, "]"] [] []⟩] } } },
  intros [ident x, ident h],
  obtain ["⟨", ident k, ",", ident e, "⟩", ":=", expr nat.rfind_opt_spec h],
  revert [ident e],
  simp [] [] ["only"] ["[", expr option.mem_def, "]"] [] []; cases [expr e', ":", expr cf.evaln k n] ["with", ident y]; simp [] [] [] [] [] []; intro [],
  { exact [expr or.inr (code.evaln_sound e)] },
  { subst [expr y],
    exact [expr or.inl (code.evaln_sound e')] }
end

end Nat.Partrec

namespace Partrec

variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable Part

open nat.partrec(code)

open Nat.Partrec.Code

-- error in Computability.Halting: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem merge'
{f g : «expr →. »(α, σ)}
(hf : partrec f)
(hg : partrec g) : «expr∃ , »((k : «expr →. »(α, σ)), «expr ∧ »(partrec k, ∀
  a, «expr ∧ »(∀
   x «expr ∈ » k a, «expr ∨ »(«expr ∈ »(x, f a), «expr ∈ »(x, g a)), «expr ↔ »((k a).dom, «expr ∨ »((f a).dom, (g a).dom))))) :=
let ⟨k, hk, H⟩ := nat.partrec.merge' (bind_decode₂_iff.1 hf) (bind_decode₂_iff.1 hg) in
begin
  let [ident k'] [] [":=", expr λ a, (k (encode a)).bind (λ n, decode σ n)],
  refine [expr ⟨k', ((nat_iff.2 hk).comp computable.encode).bind (computable.decode.of_option.comp snd).to₂, λ a, _⟩],
  suffices [] [],
  refine [expr ⟨this, ⟨λ h, (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, _⟩⟩],
  { intro [ident h],
    rw [expr bind_dom] [],
    have [ident hk] [":", expr (k (encode a)).dom] [":=", expr (H _).2.2 (by simpa [] [] ["only"] ["[", expr encodek₂, ",", expr bind_some, ",", expr coe_some, "]"] [] ["using", expr h])],
    existsi [expr hk],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_map_iff, ",", expr mem_coe, ",", expr mem_bind_iff, ",", expr option.mem_def, "]"] [] ["at", ident H],
    obtain ["⟨", ident a', ",", ident ha', ",", ident y, ",", ident hy, ",", ident e, "⟩", "|", "⟨", ident a', ",", ident ha', ",", ident y, ",", ident hy, ",", ident e, "⟩", ":=", expr (H _).1 _ ⟨hk, rfl⟩]; { simp [] [] ["only"] ["[", expr e.symm, ",", expr encodek, "]"] [] [] } },
  intros [ident x, ident h'],
  simp [] [] ["only"] ["[", expr k', ",", expr exists_prop, ",", expr mem_coe, ",", expr mem_bind_iff, ",", expr option.mem_def, "]"] [] ["at", ident h'],
  obtain ["⟨", ident n, ",", ident hn, ",", ident hx, "⟩", ":=", expr h'],
  have [] [] [":=", expr (H _).1 _ hn],
  simp [] [] [] ["[", expr mem_decode₂, ",", expr encode_injective.eq_iff, "]"] [] ["at", ident this],
  obtain ["⟨", ident a', ",", ident ha, ",", ident rfl, "⟩", "|", "⟨", ident a', ",", ident ha, ",", ident rfl, "⟩", ":=", expr this]; simp [] [] ["only"] ["[", expr encodek, "]"] [] ["at", ident hx]; rw [expr hx] ["at", ident ha],
  { exact [expr or.inl ha] },
  exact [expr or.inr ha]
end

-- error in Computability.Halting: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem merge
{f g : «expr →. »(α, σ)}
(hf : partrec f)
(hg : partrec g)
(H : ∀
 (a)
 (x «expr ∈ » f a)
 (y «expr ∈ » g a), «expr = »(x, y)) : «expr∃ , »((k : «expr →. »(α, σ)), «expr ∧ »(partrec k, ∀
  a x, «expr ↔ »(«expr ∈ »(x, k a), «expr ∨ »(«expr ∈ »(x, f a), «expr ∈ »(x, g a))))) :=
let ⟨k, hk, K⟩ := merge' hf hg in
⟨k, hk, λ
 a
 x, ⟨(K _).1 _, λ h, begin
    have [] [":", expr (k a).dom] [":=", expr (K _).2.2 (h.imp Exists.fst Exists.fst)],
    refine [expr ⟨this, _⟩],
    cases [expr h] ["with", ident h, ident h]; cases [expr (K _).1 _ ⟨this, rfl⟩] ["with", ident h', ident h'],
    { exact [expr mem_unique h' h] },
    { exact [expr (H _ _ h _ h').symm] },
    { exact [expr H _ _ h' _ h] },
    { exact [expr mem_unique h' h] }
  end⟩⟩

theorem cond {c : α → Bool} {f : α →. σ} {g : α →. σ} (hc : Computable c) (hf : Partrec f) (hg : Partrec g) :
  Partrec fun a => cond (c a) (f a) (g a) :=
  let ⟨cf, ef⟩ := exists_code.1 hf 
  let ⟨cg, eg⟩ := exists_code.1 hg
  ((eval_part.comp (Computable.cond hc (const cf) (const cg)) Computable.id).bind
        ((@Computable.decode σ _).comp snd).ofOption.to₂).of_eq$
    fun a =>
      by 
        cases c a <;> simp [ef, eg, encodek]

theorem sum_cases {f : α → Sum β γ} {g : α → β →. σ} {h : α → γ →. σ} (hf : Computable f) (hg : Partrec₂ g)
  (hh : Partrec₂ h) : @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1$
    (cond (sum_cases hf (const tt).to₂ (const ff).to₂)
          (sum_cases_left hf (option_some_iff.2 hg).to₂ (const Option.none).to₂)
          (sum_cases_right hf (const Option.none).to₂ (option_some_iff.2 hh).to₂)).of_eq$
      fun a =>
        by 
          cases f a <;> simp only [Bool.cond_tt, Bool.cond_ff]

end Partrec

/-- A computable predicate is one whose indicator function is computable. -/
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ D : DecidablePred p,
    by 
      exact Computable fun a => to_bool (p a)

/-- A recursively enumerable predicate is one which is the domain of a computable partial function.
 -/
def RePred {α} [Primcodable α] (p : α → Prop) :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()

theorem RePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : RePred p) (H : ∀ a, p a ↔ q a) : RePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

theorem Partrec.dom_re {α β} [Primcodable α] [Primcodable β] {f : α →. β} (h : Partrec f) : RePred fun a => (f a).Dom :=
  (h.map (Computable.const ()).to₂).of_eq$
    fun n =>
      Part.ext$
        fun _ =>
          by 
            simp [Part.dom_iff_mem]

theorem ComputablePred.of_eq {α} [Primcodable α] {p q : α → Prop} (hp : ComputablePred p) (H : ∀ a, p a ↔ q a) :
  ComputablePred q :=
  (funext fun a => propext (H a) : p = q) ▸ hp

namespace ComputablePred

variable {α : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable σ]

open nat.partrec(code)

open Nat.Partrec.Code Computable

theorem computable_iff {p : α → Prop} : ComputablePred p ↔ ∃ f : α → Bool, Computable f ∧ p = fun a => f a :=
  ⟨fun ⟨D, h⟩ =>
      by 
        exact ⟨_, h, funext$ fun a => propext (to_bool_iff _).symm⟩,
    by 
      rintro ⟨f, h, rfl⟩ <;>
        exact
          ⟨by 
              infer_instance,
            by 
              simpa using h⟩⟩

protected theorem Not {p : α → Prop} (hp : ComputablePred p) : ComputablePred fun a => ¬p a :=
  by 
    obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp <;>
      exact
        ⟨by 
            infer_instance,
          (cond hf (const ff) (const tt)).of_eq
            fun n =>
              by 
                dsimp 
                cases f n <;> rfl⟩

theorem to_re {p : α → Prop} (hp : ComputablePred p) : RePred p :=
  by 
    obtain ⟨f, hf, rfl⟩ := computable_iff.1 hp 
    unfold RePred 
    refine'
      (Partrec.cond hf (Decidable.Partrec.const' (Part.some ())) Partrec.none).of_eq fun n => Part.ext$ fun a => _ 
    cases a 
    cases f n <;> simp 

theorem rice (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c => eval c ∈ C) {f g} (hf : Nat.Partrec f) (hg : Nat.Partrec g)
  (fC : f ∈ C) : g ∈ C :=
  by 
    cases' h with _ h 
    skip 
    obtain ⟨c, e⟩ :=
      fixed_point₂
        (Partrec.cond (h.comp fst) ((Partrec.nat_iff.2 hg).comp snd).to₂ ((Partrec.nat_iff.2 hf).comp snd).to₂).to₂ 
    simp  at e 
    byCases' H : eval c ∈ C
    ·
      simp only [H, if_true] at e 
      rwa [←e]
    ·
      simp only [H, if_false] at e 
      rw [e] at H 
      contradiction

theorem rice₂ (C : Set code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
  (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.Univ :=
  by 
    classical <;>
      exact
        have hC : ∀ f, f ∈ C ↔ eval f ∈ eval '' C := fun f => ⟨Set.mem_image_of_mem _, fun ⟨g, hg, e⟩ => (H _ _ e).1 hg⟩
        ⟨fun h =>
            or_iff_not_imp_left.2$
              fun C0 =>
                Set.eq_univ_of_forall$
                  fun cg =>
                    let ⟨cf, fC⟩ := Set.ne_empty_iff_nonempty.1 C0
                    (hC _).2$
                      rice (eval '' C) (h.of_eq hC) (Partrec.nat_iff.1$ eval_part.comp (const cf) Computable.id)
                        (Partrec.nat_iff.1$ eval_part.comp (const cg) Computable.id) ((hC _).1 fC),
          fun h =>
            by 
              obtain rfl | rfl := h <;>
                simp [ComputablePred, Set.mem_empty_eq] <;>
                  exact
                    ⟨by 
                        infer_instance,
                      Computable.const _⟩⟩

theorem halting_problem_re n : RePred fun c => (eval c n).Dom :=
  (eval_part.comp Computable.id (Computable.const _)).dom_re

theorem halting_problem n : ¬ComputablePred fun c => (eval c n).Dom
| h => rice { f | (f n).Dom } h Nat.Partrec.zero Nat.Partrec.none trivialₓ

@[nolint decidable_classical]
theorem computable_iff_re_compl_re {p : α → Prop} [DecidablePred p] :
  ComputablePred p ↔ RePred p ∧ RePred fun a => ¬p a :=
  ⟨fun h => ⟨h.to_re, h.not.to_re⟩,
    fun ⟨h₁, h₂⟩ =>
      ⟨‹_›,
        by 
          obtain ⟨k, pk, hk⟩ := Partrec.merge (h₁.map (Computable.const tt).to₂) (h₂.map (Computable.const ff).to₂) _
          ·
            refine' Partrec.of_eq pk fun n => Part.eq_some_iff.2 _ 
            rw [hk]
            simp 
            apply Decidable.em
          ·
            intro a x hx y hy 
            simp  at hx hy 
            cases hy.1 hx.1⟩⟩

theorem computable_iff_re_compl_re' {p : α → Prop} : ComputablePred p ↔ RePred p ∧ RePred fun a => ¬p a :=
  by 
    classical <;> exact computable_iff_re_compl_re

theorem halting_problem_not_re n : ¬RePred fun c => ¬(eval c n).Dom
| h => halting_problem _$ computable_iff_re_compl_re'.2 ⟨halting_problem_re _, h⟩

end ComputablePred

namespace Nat

open Vector Part

/-- A simplified basis for `partrec`. -/
inductive partrec' : ∀ {n}, (Vector ℕ n →. ℕ) → Prop
  | prim {n f} : @primrec' n f → @partrec' n f
  | comp {m n f} (g : Finₓ n → Vector ℕ m →. ℕ) :
  partrec' f → (∀ i, partrec' (g i)) → partrec' fun v => (m_of_fn fun i => g i v) >>= f
  | rfind {n} {f : Vector ℕ (n+1) → ℕ} : @partrec' (n+1) f → partrec' fun v => rfind fun n => some (f (n::ᵥv) = 0)

end Nat

namespace Nat.Partrec'

open Vector Partrec Computable

open nat(Partrec')

open Nat.Partrec'

-- error in Computability.Halting: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_part {n f} (pf : @partrec' n f) : partrec f :=
begin
  induction [expr pf] [] [] [],
  case [ident nat.partrec'.prim, ":", ident n, ident f, ident hf] { exact [expr hf.to_prim.to_comp] },
  case [ident nat.partrec'.comp, ":", ident m, ident n, ident f, ident g, "_", "_", ident hf, ident hg] { exact [expr (vector_m_of_fn (λ
       i, hg i)).bind (hf.comp snd)] },
  case [ident nat.partrec'.rfind, ":", ident n, ident f, "_", ident hf] { have [] [] [":=", expr ((primrec.eq.comp primrec.id (primrec.const 0)).to_comp.comp (hf.comp (vector_cons.comp snd fst))).to₂.partrec₂],
    exact [expr this.rfind] }
end

theorem of_eq {n} {f g : Vector ℕ n →. ℕ} (hf : partrec' f) (H : ∀ i, f i = g i) : partrec' g :=
  (funext H : f = g) ▸ hf

theorem of_prim {n} {f : Vector ℕ n → ℕ} (hf : Primrec f) : @partrec' n f :=
  prim (Nat.Primrec'.of_prim hf)

theorem head {n : ℕ} : @partrec' n.succ (@head ℕ n) :=
  prim Nat.Primrec'.head

theorem tail {n f} (hf : @partrec' n f) : @partrec' n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @prim _ _$ Nat.Primrec'.nth i.succ).of_eq$
    fun v =>
      by 
        simp  <;> rw [←of_fn_nth v.tail] <;> congr <;> funext i <;> simp 

protected theorem bind {n f g} (hf : @partrec' n f) (hg : @partrec' (n+1) g) :
  @partrec' n fun v => (f v).bind fun a => g (a::ᵥv) :=
  (@comp n (n+1) g (fun i => Finₓ.cases f (fun i v => some (v.nth i)) i) hg
        fun i =>
          by 
            refine' Finₓ.cases _ (fun i => _) i <;> simp 
            exact prim (Nat.Primrec'.nth _)).of_eq$
    fun v =>
      by 
        simp [m_of_fn, Part.bind_assoc, pure]

protected theorem map {n f} {g : Vector ℕ (n+1) → ℕ} (hf : @partrec' n f) (hg : @partrec' (n+1) g) :
  @partrec' n fun v => (f v).map fun a => g (a::ᵥv) :=
  by 
    simp [(Part.bind_some_eq_map _ _).symm] <;> exact hf.bind hg

/-- Analogous to `nat.partrec'` for `ℕ`-valued functions, a predicate for partial recursive
  vector-valued functions.-/
def vec {n m} (f : Vector ℕ n → Vector ℕ m) :=
  ∀ i, partrec' fun v => (f v).nth i

theorem vec.prim {n m f} (hf : @Nat.Primrec'.Vec n m f) : vec f :=
  fun i => prim$ hf i

protected theorem nil {n} : @vec n 0 fun _ => nil :=
  fun i => i.elim0

protected theorem cons {n m} {f : Vector ℕ n → ℕ} {g} (hf : @partrec' n f) (hg : @vec n m g) : vec fun v => f v::ᵥg v :=
  fun i =>
    Finₓ.cases
      (by 
        simp )
      (fun i =>
        by 
          simp only [hg i, nth_cons_succ])
      i

theorem idv {n} : @vec n n id :=
  vec.prim Nat.Primrec'.idv

theorem comp' {n m f g} (hf : @partrec' m f) (hg : @vec n m g) : partrec' fun v => f (g v) :=
  (hf.comp _ hg).of_eq$
    fun v =>
      by 
        simp 

theorem comp₁ {n} (f : ℕ →. ℕ) {g : Vector ℕ n → ℕ} (hf : @partrec' 1 fun v => f v.head) (hg : @partrec' n g) :
  @partrec' n fun v => f (g v) :=
  by 
    simpa using hf.comp' (partrec'.cons hg partrec'.nil)

-- error in Computability.Halting: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rfind_opt
{n}
{f : vector exprℕ() «expr + »(n, 1) → exprℕ()}
(hf : @partrec' «expr + »(n, 1) f) : @partrec' n (λ
 v, nat.rfind_opt (λ a, of_nat (option exprℕ()) (f «expr ::ᵥ »(a, v)))) :=
«expr $ »((«expr $ »(rfind, (of_prim (primrec.nat_sub.comp (primrec.const 1) primrec.vector_head)).comp₁ (λ
    n, part.some «expr - »(1, n)) hf).bind ((prim nat.primrec'.pred).comp₁ nat.pred hf)).of_eq, λ
 v, «expr $ »(part.ext, λ b, begin
    simp [] [] ["only"] ["[", expr nat.rfind_opt, ",", expr exists_prop, ",", expr tsub_eq_zero_iff_le, ",", expr pfun.coe_val, ",", expr part.mem_bind_iff, ",", expr part.mem_some_iff, ",", expr option.mem_def, ",", expr part.mem_coe, "]"] [] [],
    refine [expr exists_congr (λ a, (and_congr (iff_of_eq _) iff.rfl).trans (and_congr_right (λ h, _)))],
    { congr,
      funext [ident n],
      simp [] [] ["only"] ["[", expr part.some_inj, ",", expr pfun.coe_val, "]"] [] [],
      cases [expr f «expr ::ᵥ »(n, v)] []; simp [] [] [] ["[", expr nat.succ_le_succ, "]"] [] []; refl },
    { have [] [] [":=", expr nat.rfind_spec h],
      simp [] [] ["only"] ["[", expr pfun.coe_val, ",", expr part.mem_some_iff, "]"] [] ["at", ident this],
      cases [expr f «expr ::ᵥ »(a, v)] ["with", ident c],
      { cases [expr this] [] },
      rw ["[", "<-", expr option.some_inj, ",", expr eq_comm, "]"] [],
      refl }
  end))

open Nat.Partrec.Code

theorem of_part : ∀ {n f}, Partrec f → @partrec' n f :=
  suffices ∀ f, Nat.Partrec f → @partrec' 1 fun v => f v.head from
    fun n f hf =>
      by 
        let g 
        swap 
        exact
          (comp₁ g (this g hf) (prim Nat.Primrec'.encode)).of_eq
            fun i =>
              by 
                dsimp only [g] <;> simp [encodek, Part.map_id']
  fun f hf =>
    by 
      obtain ⟨c, rfl⟩ := exists_code.1 hf 
      simpa [eval_eq_rfind_opt] using
        rfind_opt$
          of_prim$
            Primrec.encode_iff.2$
              evaln_prim.comp$
                (primrec.vector_head.pair (Primrec.const c)).pair$ primrec.vector_head.comp Primrec.vector_tail

theorem part_iff {n f} : @partrec' n f ↔ Partrec f :=
  ⟨to_part, of_part⟩

theorem part_iff₁ {f : ℕ →. ℕ} : (@partrec' 1 fun v => f v.head) ↔ Partrec f :=
  part_iff.trans
    ⟨fun h =>
        (h.comp$ (Primrec.vector_of_fn$ fun i => Primrec.id).to_comp).of_eq
          fun v =>
            by 
              simp only [id.def, head_of_fn],
      fun h => h.comp vector_head⟩

theorem part_iff₂ {f : ℕ → ℕ →. ℕ} : (@partrec' 2 fun v => f v.head v.tail.head) ↔ Partrec₂ f :=
  part_iff.trans
    ⟨fun h =>
        (h.comp$ vector_cons.comp fst$ vector_cons.comp snd (const nil)).of_eq
          fun v =>
            by 
              simp only [cons_head, cons_tail],
      fun h => h.comp vector_head (vector_head.comp vector_tail)⟩

theorem vec_iff {m n f} : @vec m n f ↔ Computable f :=
  ⟨fun h =>
      by 
        simpa only [of_fn_nth] using vector_of_fn fun i => to_part (h i),
    fun h i => of_part$ vector_nth.comp h (const i)⟩

end Nat.Partrec'

