import Mathbin.SetTheory.OrdinalArithmetic

/-!
# Ordinal notation

Constructive ordinal arithmetic for ordinals below `ε₀`.

We define a type `onote`, with constructors `0 : onote` and `onote.oadd e n a` representing
`ω ^ e * n + a`.
We say that `o` is in Cantor normal form - `onote.NF o` - if either `o = 0` or
`o = ω ^ e * n + a` with `a < ω ^ e` and `a` in Cantor normal form.

The type `nonote` is the type of ordinals below `ε₀` in Cantor normal form.
Various operations (addition, subtraction, multiplication, power function)
are defined on `onote` and `nonote`.
-/


open Ordinal

open_locale Ordinal

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
/-- Recursive definition of an ordinal notation. `zero` denotes the
  ordinal 0, and `oadd e n a` is intended to refer to `ω^e * n + a`.
  For this to be valid Cantor normal form, we must have the exponents
  decrease to the right, but we can't state this condition until we've
  defined `repr`, so it is a separate definition `NF`. -/ @[derive #[expr decidable_eq]] inductive onote : Type
| zero : onote
| oadd : onote → «exprℕ+»() → onote → onote

namespace Onote

/-- Notation for 0 -/
instance : HasZero Onote :=
  ⟨zero⟩

@[simp]
theorem zero_def : zero = 0 :=
  rfl

instance : Inhabited Onote :=
  ⟨0⟩

/-- Notation for 1 -/
instance : HasOne Onote :=
  ⟨oadd 0 1 0⟩

/-- Notation for ω -/
def omega : Onote :=
  oadd 1 1 0

/-- The ordinal denoted by a notation -/
@[simp]
noncomputable def reprₓ : Onote → Ordinal.{0}
| 0 => 0
| oadd e n a => ((ω^reprₓ e)*n)+reprₓ a

/-- Auxiliary definition to print an ordinal notation -/
def to_string_aux1 (e : Onote) (n : ℕ) (s : Stringₓ) : Stringₓ :=
  if e = 0 then _root_.to_string n else
    (if e = 1 then "ω" else "ω^(" ++ s ++ ")") ++ if n = 1 then "" else "*" ++ _root_.to_string n

/-- Print an ordinal notation -/
def toString : Onote → Stringₓ
| zero => "0"
| oadd e n 0 => to_string_aux1 e n (toString e)
| oadd e n a => to_string_aux1 e n (toString e) ++ " + " ++ toString a

/-- Print an ordinal notation -/
def repr' : Onote → Stringₓ
| zero => "0"
| oadd e n a => "(oadd " ++ repr' e ++ " " ++ _root_.to_string (n : ℕ) ++ " " ++ repr' a ++ ")"

instance : HasToString Onote :=
  ⟨toString⟩

instance : HasRepr Onote :=
  ⟨repr'⟩

instance : Preorderₓ Onote :=
  { le := fun x y => reprₓ x ≤ reprₓ y, lt := fun x y => reprₓ x < reprₓ y, le_refl := fun a => @le_reflₓ Ordinal _ _,
    le_trans := fun a b c => @le_transₓ Ordinal _ _ _ _,
    lt_iff_le_not_le := fun a b => @lt_iff_le_not_leₓ Ordinal _ _ _ }

theorem lt_def {x y : Onote} : x < y ↔ reprₓ x < reprₓ y :=
  Iff.rfl

theorem le_def {x y : Onote} : x ≤ y ↔ reprₓ x ≤ reprₓ y :=
  Iff.rfl

/-- Convert a `nat` into an ordinal -/
@[simp]
def of_nat : ℕ → Onote
| 0 => 0
| Nat.succ n => oadd 0 n.succ_pnat 0

@[simp]
theorem of_nat_one : of_nat 1 = 1 :=
  rfl

@[simp]
theorem repr_of_nat (n : ℕ) : reprₓ (of_nat n) = n :=
  by 
    cases n <;> simp 

@[simp]
theorem repr_one : reprₓ 1 = 1 :=
  by 
    simpa using repr_of_nat 1

theorem omega_le_oadd e n a : (ω^reprₓ e) ≤ reprₓ (oadd e n a) :=
  by 
    unfold reprₓ 
    refine' le_transₓ _ (le_add_right _ _)
    simpa using (mul_le_mul_iff_left$ power_pos (reprₓ e) omega_pos).2 (nat_cast_le.2 n.2)

theorem oadd_pos e n a : 0 < oadd e n a :=
  @lt_of_lt_of_leₓ _ _ _ _ _ (power_pos _ omega_pos) (omega_le_oadd _ _ _)

/-- Compare ordinal notations -/
def cmp : Onote → Onote → Ordering
| 0, 0 => Ordering.eq
| _, 0 => Ordering.gt
| 0, _ => Ordering.lt
| o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂) => (cmp e₁ e₂).orElse$ (_root_.cmp (n₁ : ℕ) n₂).orElse (cmp a₁ a₂)

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_cmp_eq : ∀ {o₁ o₂}, «expr = »(cmp o₁ o₂, ordering.eq) → «expr = »(o₁, o₂)
| 0, 0, h := rfl
| oadd e n a, 0, h := by injection [expr h] []
| 0, oadd e n a, h := by injection [expr h] []
| o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h := begin
  revert [ident h],
  simp [] [] [] ["[", expr cmp, "]"] [] [],
  cases [expr h₁, ":", expr cmp e₁ e₂] []; intro [ident h]; try { cases [expr h] [] },
  have [] [] [":=", expr eq_of_cmp_eq h₁],
  subst [expr e₂],
  revert [ident h],
  cases [expr h₂, ":", expr _root_.cmp (n₁ : exprℕ()) n₂] []; intro [ident h]; try { cases [expr h] [] },
  have [] [] [":=", expr eq_of_cmp_eq h],
  subst [expr a₂],
  rw ["[", expr _root_.cmp, ",", expr cmp_using_eq_eq, "]"] ["at", ident h₂],
  have [] [] [":=", expr subtype.eq (eq_of_incomp h₂)],
  subst [expr n₂],
  simp [] [] [] [] [] []
end

theorem zero_lt_one : (0 : Onote) < 1 :=
  by 
    rw [lt_def, reprₓ, repr_one] <;> exact zero_lt_one

/-- `NF_below o b` says that `o` is a normal form ordinal notation
  satisfying `repr o < ω ^ b`. -/
inductive NF_below : Onote → Ordinal.{0} → Prop
  | zero {b} : NF_below 0 b
  | oadd' {e n a eb b} : NF_below e eb → NF_below a (reprₓ e) → reprₓ e < b → NF_below (oadd e n a) b

/-- A normal form ordinal notation has the form

     ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ... ω ^ aₖ * nₖ
  where `a₁ > a₂ > ... > aₖ` and all the `aᵢ` are
  also in normal form.

  We will essentially only be interested in normal form
  ordinal notations, but to avoid complicating the algorithms
  we define everything over general ordinal notations and
  only prove correctness with normal form as an invariant. -/
class NF (o : Onote) : Prop where 
  out : Exists (NF_below o)

attribute [pp_nodot] NF

instance NF.zero : NF 0 :=
  ⟨⟨0, NF_below.zero⟩⟩

theorem NF_below.oadd {e n a b} : NF e → NF_below a (reprₓ e) → reprₓ e < b → NF_below (oadd e n a) b
| ⟨⟨eb, h⟩⟩ => NF_below.oadd' h

theorem NF_below.fst {e n a b} (h : NF_below (oadd e n a) b) : NF e :=
  by 
    cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact ⟨⟨_, h₁⟩⟩

theorem NF.fst {e n a} : NF (oadd e n a) → NF e
| ⟨⟨b, h⟩⟩ => h.fst

theorem NF_below.snd {e n a b} (h : NF_below (oadd e n a) b) : NF_below a (reprₓ e) :=
  by 
    cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact h₂

theorem NF.snd' {e n a} : NF (oadd e n a) → NF_below a (reprₓ e)
| ⟨⟨b, h⟩⟩ => h.snd

theorem NF.snd {e n a} (h : NF (oadd e n a)) : NF a :=
  ⟨⟨_, h.snd'⟩⟩

theorem NF.oadd {e a} (h₁ : NF e) n (h₂ : NF_below a (reprₓ e)) : NF (oadd e n a) :=
  ⟨⟨_, NF_below.oadd h₁ h₂ (Ordinal.lt_succ_self _)⟩⟩

instance NF.oadd_zero e n [h : NF e] : NF (oadd e n 0) :=
  h.oadd _ NF_below.zero

theorem NF_below.lt {e n a b} (h : NF_below (oadd e n a) b) : reprₓ e < b :=
  by 
    cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact h₃

theorem NF_below_zero : ∀ {o}, NF_below o 0 ↔ o = 0
| 0 => ⟨fun _ => rfl, fun _ => NF_below.zero⟩
| oadd e n a => ⟨fun h => (not_le_of_lt h.lt).elim (Ordinal.zero_le _), fun e => e.symm ▸ NF_below.zero⟩

theorem NF.zero_of_zero {e n a} (h : NF (oadd e n a)) (e0 : e = 0) : a = 0 :=
  by 
    simpa [e0, NF_below_zero] using h.snd'

theorem NF_below.repr_lt {o b} (h : NF_below o b) : reprₓ o < (ω^b) :=
  by 
    induction' h with _ e n a eb b h₁ h₂ h₃ _ IH
    ·
      exact power_pos _ omega_pos
    ·
      rw [reprₓ]
      refine' lt_of_lt_of_leₓ ((Ordinal.add_lt_add_iff_left _).2 IH) _ 
      rw [←mul_succ]
      refine' le_transₓ (mul_le_mul_left _$ Ordinal.succ_le.2$ nat_lt_omega _) _ 
      rw [←power_succ]
      exact power_le_power_right omega_pos (Ordinal.succ_le.2 h₃)

theorem NF_below.mono {o b₁ b₂} (bb : b₁ ≤ b₂) (h : NF_below o b₁) : NF_below o b₂ :=
  by 
    induction' h with _ e n a eb b h₁ h₂ h₃ _ IH <;> constructor 
    exacts[h₁, h₂, lt_of_lt_of_leₓ h₃ bb]

theorem NF.below_of_lt {e n a b} (H : reprₓ e < b) : NF (oadd e n a) → NF_below (oadd e n a) b
| ⟨⟨b', h⟩⟩ =>
  by 
    cases' h with _ _ _ _ eb _ h₁ h₂ h₃ <;> exact NF_below.oadd' h₁ h₂ H

theorem NF.below_of_lt' : ∀ {o b}, reprₓ o < (ω^b) → NF o → NF_below o b
| 0, b, H, _ => NF_below.zero
| oadd e n a, b, H, h =>
  h.below_of_lt$ (power_lt_power_iff_right one_lt_omega).1$ lt_of_le_of_ltₓ (omega_le_oadd _ _ _) H

theorem NF_below_of_nat : ∀ n, NF_below (of_nat n) 1
| 0 => NF_below.zero
| Nat.succ n => NF_below.oadd NF.zero NF_below.zero Ordinal.zero_lt_one

instance NF_of_nat n : NF (of_nat n) :=
  ⟨⟨_, NF_below_of_nat n⟩⟩

instance NF_one : NF 1 :=
  by 
    rw [←of_nat_one] <;> infer_instance

theorem oadd_lt_oadd_1 {e₁ n₁ o₁ e₂ n₂ o₂} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) : oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  @lt_of_lt_of_leₓ _ _ _ _ _ (h₁.below_of_lt h).repr_lt (omega_le_oadd _ _ _)

theorem oadd_lt_oadd_2 {e o₁ o₂ : Onote} {n₁ n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : (n₁ : ℕ) < n₂) :
  oadd e n₁ o₁ < oadd e n₂ o₂ :=
  by 
    simp [lt_def]
    refine' lt_of_lt_of_leₓ ((Ordinal.add_lt_add_iff_left _).2 h₁.snd'.repr_lt) (le_transₓ _ (le_add_right _ _))
    rwa [←mul_succ, mul_le_mul_iff_left (power_pos _ omega_pos), Ordinal.succ_le, nat_cast_lt]

theorem oadd_lt_oadd_3 {e n a₁ a₂} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ :=
  by 
    rw [lt_def]
    unfold reprₓ 
    exact (Ordinal.add_lt_add_iff_left _).2 h

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cmp_compares : ∀ (a b : onote) [NF a] [NF b], (cmp a b).compares a b
| 0, 0, h₁, h₂ := rfl
| oadd e n a, 0, h₁, h₂ := oadd_pos _ _ _
| 0, oadd e n a, h₁, h₂ := oadd_pos _ _ _
| o₁@(oadd e₁ n₁ a₁), o₂@(oadd e₂ n₂ a₂), h₁, h₂ := begin
  rw [expr cmp] [],
  have [ident IHe] [] [":=", expr @cmp_compares _ _ h₁.fst h₂.fst],
  cases [expr cmp e₁ e₂] [],
  case [ident ordering.lt] { exact [expr oadd_lt_oadd_1 h₁ IHe] },
  case [ident ordering.gt] { exact [expr oadd_lt_oadd_1 h₂ IHe] },
  change [expr «expr = »(e₁, e₂)] [] ["at", ident IHe],
  subst [expr IHe],
  unfold [ident _root_.cmp] [],
  cases [expr nh, ":", expr cmp_using ((«expr < »)) (n₁ : exprℕ()) n₂] [],
  case [ident ordering.lt] { rw [expr cmp_using_eq_lt] ["at", ident nh],
    exact [expr oadd_lt_oadd_2 h₁ nh] },
  case [ident ordering.gt] { rw [expr cmp_using_eq_gt] ["at", ident nh],
    exact [expr oadd_lt_oadd_2 h₂ nh] },
  rw [expr cmp_using_eq_eq] ["at", ident nh],
  have [] [] [":=", expr subtype.eq (eq_of_incomp nh)],
  subst [expr n₂],
  have [ident IHa] [] [":=", expr @cmp_compares _ _ h₁.snd h₂.snd],
  cases [expr cmp a₁ a₂] [],
  case [ident ordering.lt] { exact [expr oadd_lt_oadd_3 IHa] },
  case [ident ordering.gt] { exact [expr oadd_lt_oadd_3 IHa] },
  change [expr «expr = »(a₁, a₂)] [] ["at", ident IHa],
  subst [expr IHa],
  exact [expr rfl]
end

theorem repr_inj {a b} [NF a] [NF b] : reprₓ a = reprₓ b ↔ a = b :=
  ⟨match cmp a b, cmp_compares a b with 
    | Ordering.lt, (h : reprₓ a < reprₓ b), e => (ne_of_ltₓ h e).elim
    | Ordering.gt, (h : reprₓ a > reprₓ b), e => (ne_of_gtₓ h e).elim
    | Ordering.eq, h, e => h,
    congr_argₓ _⟩

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem NF.of_dvd_omega_power
{b e n a}
(h : NF (oadd e n a))
(d : «expr ∣ »(«expr ^ »(exprω(), b), repr (oadd e n a))) : «expr ∧ »(«expr ≤ »(b, repr e), «expr ∣ »(«expr ^ »(exprω(), b), repr a)) :=
begin
  have [] [] [":=", expr mt repr_inj.1 (λ h, by injection [expr h] [] : «expr ≠ »(oadd e n a, 0))],
  have [ident L] [] [":=", expr le_of_not_lt (λ l, not_le_of_lt (h.below_of_lt l).repr_lt (le_of_dvd this d))],
  simp [] [] [] [] [] ["at", ident d],
  exact [expr ⟨L, «expr $ »(dvd_add_iff, (power_dvd_power _ L).mul_right _).1 d⟩]
end

theorem NF.of_dvd_omega {e n a} (h : NF (oadd e n a)) : ω ∣ reprₓ (oadd e n a) → reprₓ e ≠ 0 ∧ ω ∣ reprₓ a :=
  by 
    rw [←power_one ω, ←one_le_iff_ne_zero] <;> exact h.of_dvd_omega_power

/-- `top_below b o` asserts that the largest exponent in `o`, if
  it exists, is less than `b`. This is an auxiliary definition
  for decidability of `NF`. -/
def top_below b : Onote → Prop
| 0 => True
| oadd e n a => cmp e b = Ordering.lt

instance decidable_top_below : DecidableRel top_below :=
  by 
    intro b o <;> cases o <;> delta' top_below <;> infer_instance

theorem NF_below_iff_top_below {b} [NF b] : ∀ {o}, NF_below o (reprₓ b) ↔ NF o ∧ top_below b o
| 0 => ⟨fun h => ⟨⟨⟨_, h⟩⟩, trivialₓ⟩, fun _ => NF_below.zero⟩
| oadd e n a =>
  ⟨fun h => ⟨⟨⟨_, h⟩⟩, (@cmp_compares _ b h.fst _).eq_lt.2 h.lt⟩,
    fun ⟨h₁, h₂⟩ => h₁.below_of_lt$ (@cmp_compares _ b h₁.fst _).eq_lt.1 h₂⟩

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance decidable_NF : decidable_pred NF
| 0 := is_true NF.zero
| oadd e n a := begin
  have [] [] [":=", expr decidable_NF e],
  have [] [] [":=", expr decidable_NF a],
  resetI,
  apply [expr decidable_of_iff «expr ∧ »(NF e, «expr ∧ »(NF a, top_below e a))],
  abstract [] { rw ["<-", expr and_congr_right (λ h, @NF_below_iff_top_below _ h _)] [],
    exact [expr ⟨λ ⟨h₁, h₂⟩, NF.oadd h₁ n h₂, λ h, ⟨h.fst, h.snd'⟩⟩] }
end

/-- Addition of ordinal notations (correct only for normal input) -/
def add : Onote → Onote → Onote
| 0, o => o
| oadd e n a, o =>
  match add a o with 
  | 0 => oadd e n 0
  | o'@(oadd e' n' a') =>
    match cmp e e' with 
    | Ordering.lt => o'
    | Ordering.eq => oadd e (n+n') a'
    | Ordering.gt => oadd e n o'

instance : Add Onote :=
  ⟨add⟩

@[simp]
theorem zero_addₓ (o : Onote) : (0+o) = o :=
  rfl

theorem oadd_add e n a o : (oadd e n a+o) = add._match_1 e n (a+o) :=
  rfl

/-- Subtraction of ordinal notations (correct only for normal input) -/
def sub : Onote → Onote → Onote
| 0, o => 0
| o, 0 => o
| o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ =>
  match cmp e₁ e₂ with 
  | Ordering.lt => 0
  | Ordering.gt => o₁
  | Ordering.eq =>
    match (n₁ : ℕ) - n₂ with 
    | 0 => if n₁ = n₂ then sub a₁ a₂ else 0
    | Nat.succ k => oadd e₁ k.succ_pnat a₁

instance : Sub Onote :=
  ⟨sub⟩

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_NF_below {b} : ∀ {o₁ o₂}, NF_below o₁ b → NF_below o₂ b → NF_below «expr + »(o₁, o₂) b
| 0, o, h₁, h₂ := h₂
| oadd e n a, o, h₁, h₂ := begin
  have [ident h'] [] [":=", expr add_NF_below «expr $ »(h₁.snd.mono, le_of_lt h₁.lt) h₂],
  simp [] [] [] ["[", expr oadd_add, "]"] [] [],
  cases [expr «expr + »(a, o)] ["with", ident e', ident n', ident a'],
  { exact [expr NF_below.oadd h₁.fst NF_below.zero h₁.lt] },
  simp [] [] [] ["[", expr add, "]"] [] [],
  have [] [] [":=", expr @cmp_compares _ _ h₁.fst h'.fst],
  cases [expr cmp e e'] []; simp [] [] [] ["[", expr add, "]"] [] [],
  { exact [expr h'] },
  { simp [] [] [] [] [] ["at", ident this],
    subst [expr e'],
    exact [expr NF_below.oadd h'.fst h'.snd h'.lt] },
  { exact [expr NF_below.oadd h₁.fst (NF.below_of_lt this ⟨⟨_, h'⟩⟩) h₁.lt] }
end

instance add_NF o₁ o₂ : ∀ [NF o₁] [NF o₂], NF (o₁+o₂)
| ⟨⟨b₁, h₁⟩⟩, ⟨⟨b₂, h₂⟩⟩ =>
  ⟨(b₁.le_total b₂).elim (fun h => ⟨b₂, add_NF_below (h₁.mono h) h₂⟩) fun h => ⟨b₁, add_NF_below h₁ (h₂.mono h)⟩⟩

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem repr_add : ∀ (o₁ o₂) [NF o₁] [NF o₂], «expr = »(repr «expr + »(o₁, o₂), «expr + »(repr o₁, repr o₂))
| 0, o, h₁, h₂ := by simp [] [] [] [] [] []
| oadd e n a, o, h₁, h₂ := begin
  haveI [] [] [":=", expr h₁.snd],
  have [ident h'] [] [":=", expr repr_add a o],
  conv ["at", ident h'] ["in", expr «expr + »(_, o)] { simp [] ["[", expr («expr + »), "]"] [] },
  have [ident nf] [] [":=", expr onote.add_NF a o],
  conv ["at", ident nf] ["in", expr «expr + »(_, o)] { simp [] ["[", expr («expr + »), "]"] [] },
  conv [] ["in", expr «expr + »(_, o)] { simp [] ["[", expr («expr + »), ",", expr add, "]"] [] },
  cases [expr add a o] ["with", ident e', ident n', ident a']; simp [] [] [] ["[", expr add, ",", expr h'.symm, ",", expr add_assoc, "]"] [] [],
  have [] [] [":=", expr h₁.fst],
  haveI [] [] [":=", expr nf.fst],
  have [ident ee] [] [":=", expr cmp_compares e e'],
  cases [expr cmp e e'] []; simp [] [] [] ["[", expr add, "]"] [] [],
  { rw ["[", "<-", expr add_assoc, ",", expr @add_absorp _ (repr e') «expr * »(«expr ^ »(exprω(), repr e'), (n' : exprℕ())), "]"] [],
    { have [] [] [":=", expr (h₁.below_of_lt ee).repr_lt],
      unfold [ident repr] ["at", ident this],
      exact [expr lt_of_le_of_lt (le_add_right _ _) this] },
    { simpa [] [] [] [] [] ["using", expr «expr $ »(mul_le_mul_iff_left, power_pos (repr e') omega_pos).2 (nat_cast_le.2 n'.pos)] } },
  { change [expr «expr = »(e, e')] [] ["at", ident ee],
    substI [expr e'],
    rw ["[", "<-", expr add_assoc, ",", "<-", expr ordinal.mul_add, ",", "<-", expr nat.cast_add, "]"] [] }
end

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sub_NF_below : ∀ {o₁ o₂ b}, NF_below o₁ b → NF o₂ → NF_below «expr - »(o₁, o₂) b
| 0, o, b, h₁, h₂ := by cases [expr o] []; exact [expr NF_below.zero]
| oadd e n a, 0, b, h₁, h₂ := h₁
| oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, b, h₁, h₂ := begin
  have [ident h'] [] [":=", expr sub_NF_below h₁.snd h₂.snd],
  simp [] [] [] ["[", expr has_sub.sub, ",", expr sub, "]"] [] ["at", ident h', "⊢"],
  have [] [] [":=", expr @cmp_compares _ _ h₁.fst h₂.fst],
  cases [expr cmp e₁ e₂] []; simp [] [] [] ["[", expr sub, "]"] [] [],
  { apply [expr NF_below.zero] },
  { simp [] [] [] [] [] ["at", ident this],
    subst [expr e₂],
    cases [expr mn, ":", expr «expr - »((n₁ : exprℕ()), n₂)] []; simp [] [] [] ["[", expr sub, "]"] [] [],
    { by_cases [expr en, ":", expr «expr = »(n₁, n₂)]; simp [] [] [] ["[", expr en, "]"] [] [],
      { exact [expr h'.mono (le_of_lt h₁.lt)] },
      { exact [expr NF_below.zero] } },
    { exact [expr NF_below.oadd h₁.fst h₁.snd h₁.lt] } },
  { exact [expr h₁] }
end

instance sub_NF o₁ o₂ : ∀ [NF o₁] [NF o₂], NF (o₁ - o₂)
| ⟨⟨b₁, h₁⟩⟩, h₂ => ⟨⟨b₁, sub_NF_below h₁ h₂⟩⟩

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem repr_sub : ∀ (o₁ o₂) [NF o₁] [NF o₂], «expr = »(repr «expr - »(o₁, o₂), «expr - »(repr o₁, repr o₂))
| 0, o, h₁, h₂ := by cases [expr o] []; exact [expr (ordinal.zero_sub _).symm]
| oadd e n a, 0, h₁, h₂ := (ordinal.sub_zero _).symm
| oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ := begin
  haveI [] [] [":=", expr h₁.snd],
  haveI [] [] [":=", expr h₂.snd],
  have [ident h'] [] [":=", expr repr_sub a₁ a₂],
  conv ["at", ident h'] ["in", expr «expr - »(a₁, a₂)] { simp [] ["[", expr has_sub.sub, "]"] [] },
  have [ident nf] [] [":=", expr onote.sub_NF a₁ a₂],
  conv ["at", ident nf] ["in", expr «expr - »(a₁, a₂)] { simp [] ["[", expr has_sub.sub, "]"] [] },
  conv [] ["in", expr «expr - »(_, oadd _ _ _)] { simp [] ["[", expr has_sub.sub, ",", expr sub, "]"] [] },
  have [ident ee] [] [":=", expr @cmp_compares _ _ h₁.fst h₂.fst],
  cases [expr cmp e₁ e₂] [],
  { rw ["[", expr ordinal.sub_eq_zero_iff_le.2, "]"] [],
    { refl },
    exact [expr le_of_lt (oadd_lt_oadd_1 h₁ ee)] },
  { change [expr «expr = »(e₁, e₂)] [] ["at", ident ee],
    substI [expr e₂],
    unfold [ident sub._match_1] [],
    cases [expr mn, ":", expr «expr - »((n₁ : exprℕ()), n₂)] []; dsimp ["only"] ["[", expr sub._match_2, "]"] [] [],
    { by_cases [expr en, ":", expr «expr = »(n₁, n₂)],
      { simp [] [] [] ["[", expr en, "]"] [] [],
        rwa ["[", expr add_sub_add_cancel, "]"] [] },
      { simp [] [] [] ["[", expr en, ",", "-", ident repr, "]"] [] [],
        exact [expr «expr $ »(ordinal.sub_eq_zero_iff_le.2, «expr $ »(le_of_lt, «expr $ »(oadd_lt_oadd_2 h₁, lt_of_le_of_ne (tsub_eq_zero_iff_le.1 mn) (mt pnat.eq en)))).symm] } },
    { simp [] [] [] ["[", expr nat.succ_pnat, ",", "-", ident nat.cast_succ, "]"] [] [],
      rw ["[", expr «expr $ »(tsub_eq_iff_eq_add_of_le, «expr $ »(le_of_lt, nat.lt_of_sub_eq_succ mn)).1 mn, ",", expr add_comm, ",", expr nat.cast_add, ",", expr ordinal.mul_add, ",", expr add_assoc, ",", expr add_sub_add_cancel, "]"] [],
      refine [expr «expr $ »(ordinal.sub_eq_of_add_eq, «expr $ »(add_absorp h₂.snd'.repr_lt, le_trans _ (le_add_right _ _))).symm],
      simpa [] [] [] [] [] ["using", expr mul_le_mul_left _ «expr $ »(nat_cast_le.2, nat.succ_pos _)] } },
  { exact [expr «expr $ »(ordinal.sub_eq_of_add_eq, «expr $ »(add_absorp (h₂.below_of_lt ee).repr_lt, omega_le_oadd _ _ _)).symm] }
end

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : Onote → Onote → Onote
| 0, _ => 0
| _, 0 => 0
| o₁@(oadd e₁ n₁ a₁), oadd e₂ n₂ a₂ => if e₂ = 0 then oadd e₁ (n₁*n₂) a₁ else oadd (e₁+e₂) n₂ (mul o₁ a₂)

instance : Mul Onote :=
  ⟨mul⟩

@[simp]
theorem zero_mul (o : Onote) : (0*o) = 0 :=
  by 
    cases o <;> rfl

@[simp]
theorem mul_zero (o : Onote) : (o*0) = 0 :=
  by 
    cases o <;> rfl

theorem oadd_mul e₁ n₁ a₁ e₂ n₂ a₂ :
  (oadd e₁ n₁ a₁*oadd e₂ n₂ a₂) = if e₂ = 0 then oadd e₁ (n₁*n₂) a₁ else oadd (e₁+e₂) n₂ (oadd e₁ n₁ a₁*a₂) :=
  rfl

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem oadd_mul_NF_below
{e₁ n₁ a₁ b₁}
(h₁ : NF_below (oadd e₁ n₁ a₁) b₁) : ∀
{o₂ b₂}, NF_below o₂ b₂ → NF_below «expr * »(oadd e₁ n₁ a₁, o₂) «expr + »(repr e₁, b₂)
| 0, b₂, h₂ := NF_below.zero
| oadd e₂ n₂ a₂, b₂, h₂ := begin
  have [ident IH] [] [":=", expr oadd_mul_NF_below h₂.snd],
  by_cases [expr e0, ":", expr «expr = »(e₂, 0)]; simp [] [] [] ["[", expr e0, ",", expr oadd_mul, "]"] [] [],
  { apply [expr NF_below.oadd h₁.fst h₁.snd],
    simpa [] [] [] [] [] ["using", expr (add_lt_add_iff_left (repr e₁)).2 (lt_of_le_of_lt (ordinal.zero_le _) h₂.lt)] },
  { haveI [] [] [":=", expr h₁.fst],
    haveI [] [] [":=", expr h₂.fst],
    apply [expr NF_below.oadd],
    apply_instance,
    { rwa [expr repr_add] [] },
    { rw ["[", expr repr_add, ",", expr ordinal.add_lt_add_iff_left, "]"] [],
      exact [expr h₂.lt] } }
end

instance mul_NF : ∀ o₁ o₂ [NF o₁] [NF o₂], NF (o₁*o₂)
| 0, o, h₁, h₂ =>
  by 
    cases o <;> exact NF.zero
| oadd e n a, o, ⟨⟨b₁, hb₁⟩⟩, ⟨⟨b₂, hb₂⟩⟩ => ⟨⟨_, oadd_mul_NF_below hb₁ hb₂⟩⟩

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem repr_mul : ∀ (o₁ o₂) [NF o₁] [NF o₂], «expr = »(repr «expr * »(o₁, o₂), «expr * »(repr o₁, repr o₂))
| 0, o, h₁, h₂ := by cases [expr o] []; exact [expr (ordinal.zero_mul _).symm]
| oadd e₁ n₁ a₁, 0, h₁, h₂ := (ordinal.mul_zero _).symm
| oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h₁, h₂ := begin
  have [ident IH] [":", expr «expr = »(repr (mul _ _), _)] [":=", expr @repr_mul _ _ h₁ h₂.snd],
  conv [] [] { to_lhs,
    simp [] ["[", expr («expr * »), "]"] [] },
  have [ident ao] [":", expr «expr = »(«expr + »(repr a₁, «expr * »(«expr ^ »(exprω(), repr e₁), (n₁ : exprℕ()))), «expr * »(«expr ^ »(exprω(), repr e₁), (n₁ : exprℕ())))] [],
  { apply [expr add_absorp h₁.snd'.repr_lt],
    simpa [] [] [] [] [] ["using", expr «expr $ »(mul_le_mul_iff_left, power_pos _ omega_pos).2 (nat_cast_le.2 n₁.2)] },
  by_cases [expr e0, ":", expr «expr = »(e₂, 0)]; simp [] [] [] ["[", expr e0, ",", expr mul, "]"] [] [],
  { cases [expr nat.exists_eq_succ_of_ne_zero n₂.ne_zero] ["with", ident x, ident xe],
    simp [] [] [] ["[", expr h₂.zero_of_zero e0, ",", expr xe, ",", "-", ident nat.cast_succ, "]"] [] [],
    rw ["[", "<-", expr nat_cast_succ x, ",", expr add_mul_succ _ ao, ",", expr mul_assoc, "]"] [] },
  { haveI [] [] [":=", expr h₁.fst],
    haveI [] [] [":=", expr h₂.fst],
    simp [] [] [] ["[", expr IH, ",", expr repr_add, ",", expr power_add, ",", expr ordinal.mul_add, "]"] [] [],
    rw ["<-", expr mul_assoc] [],
    congr' [2] [],
    have [] [] [":=", expr mt repr_inj.1 e0],
    rw ["[", expr add_mul_limit ao (power_is_limit_left omega_is_limit this), ",", expr mul_assoc, ",", expr mul_omega_dvd (nat_cast_pos.2 n₁.pos) (nat_lt_omega _), "]"] [],
    simpa [] [] [] [] [] ["using", expr power_dvd_power exprω() (one_le_iff_ne_zero.2 this)] }
end

/-- Calculate division and remainder of `o` mod ω.
  `split' o = (a, n)` means `o = ω * a + n`. -/
def split' : Onote → Onote × ℕ
| 0 => (0, 0)
| oadd e n a =>
  if e = 0 then (0, n) else
    let (a', m) := split' a
    (oadd (e - 1) n a', m)

/-- Calculate division and remainder of `o` mod ω.
  `split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : Onote → Onote × ℕ
| 0 => (0, 0)
| oadd e n a =>
  if e = 0 then (0, n) else
    let (a', m) := split a
    (oadd e n a', m)

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : Onote) : Onote → Onote
| 0 => 0
| oadd e n a => oadd (x+e) n (scale a)

/-- `mul_nat o n` is the ordinal notation for `o * n`. -/
def mul_nat : Onote → ℕ → Onote
| 0, m => 0
| _, 0 => 0
| oadd e n a, m+1 => oadd e (n*m.succ_pnat) a

/-- Auxiliary definition to compute the ordinal notation for the ordinal
exponentiation in `power` -/
def power_aux (e a0 a : Onote) : ℕ → ℕ → Onote
| _, 0 => 0
| 0, m+1 => oadd e m.succ_pnat 0
| k+1, m => scale (e+mul_nat a0 k) a+power_aux k m

/-- `power o₁ o₂` calculates the ordinal notation for
  the ordinal exponential `o₁ ^ o₂`. -/
def power (o₁ o₂ : Onote) : Onote :=
  match split o₁ with 
  | (0, 0) => if o₂ = 0 then 1 else 0
  | (0, 1) => 1
  | (0, m+1) =>
    let (b', k) := split' o₂ 
    oadd b' (@Pow.pow ℕ+ _ _ m.succ_pnat k) 0
  | (a@(oadd a0 _ _), m) =>
    match split o₂ with 
    | (b, 0) => oadd (a0*b) 1 0
    | (b, k+1) =>
      let eb := a0*b 
      scale (eb+mul_nat a0 k) a+power_aux eb a0 (mul_nat a m) k m

instance : Pow Onote Onote :=
  ⟨power⟩

theorem power_def (o₁ o₂ : Onote) : (o₁^o₂) = power._match_1 o₂ (split o₁) :=
  rfl

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem split_eq_scale_split' : ∀ {o o' m} [NF o], «expr = »(split' o, (o', m)) → «expr = »(split o, (scale 1 o', m))
| 0, o', m, h, p := by injection [expr p] []; substs [ident o', ident m]; refl
| oadd e n a, o', m, h, p := begin
  by_cases [expr e0, ":", expr «expr = »(e, 0)]; simp [] [] [] ["[", expr e0, ",", expr split, ",", expr split', "]"] [] ["at", ident p, "⊢"],
  { rcases [expr p, "with", "⟨", ident rfl, ",", ident rfl, "⟩"],
    exact [expr ⟨rfl, rfl⟩] },
  { revert [ident p],
    cases [expr h', ":", expr split' a] ["with", ident a', ident m'],
    haveI [] [] [":=", expr h.fst],
    haveI [] [] [":=", expr h.snd],
    simp [] [] [] ["[", expr split_eq_scale_split' h', ",", expr split, ",", expr split', "]"] [] [],
    have [] [":", expr «expr = »(«expr + »(1, «expr - »(e, 1)), e)] [],
    { refine [expr repr_inj.1 _],
      simp [] [] [] [] [] [],
      have [] [] [":=", expr mt repr_inj.1 e0],
      exact [expr ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this)] },
    intros [],
    substs [ident o', ident m],
    simp [] [] [] ["[", expr scale, ",", expr this, "]"] [] [] }
end

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem NF_repr_split' : ∀
{o o' m}
[NF o], «expr = »(split' o, (o', m)) → «expr ∧ »(NF o', «expr = »(repr o, «expr + »(«expr * »(exprω(), repr o'), m)))
| 0, o', m, h, p := by injection [expr p] []; substs [ident o', ident m]; simp [] [] [] ["[", expr NF.zero, "]"] [] []
| oadd e n a, o', m, h, p := begin
  by_cases [expr e0, ":", expr «expr = »(e, 0)]; simp [] [] [] ["[", expr e0, ",", expr split, ",", expr split', "]"] [] ["at", ident p, "⊢"],
  { rcases [expr p, "with", "⟨", ident rfl, ",", ident rfl, "⟩"],
    simp [] [] [] ["[", expr h.zero_of_zero e0, ",", expr NF.zero, "]"] [] [] },
  { revert [ident p],
    cases [expr h', ":", expr split' a] ["with", ident a', ident m'],
    haveI [] [] [":=", expr h.fst],
    haveI [] [] [":=", expr h.snd],
    cases [expr NF_repr_split' h'] ["with", ident IH₁, ident IH₂],
    simp [] [] [] ["[", expr IH₂, ",", expr split', "]"] [] [],
    intros [],
    substs [ident o', ident m],
    have [] [":", expr «expr = »(«expr ^ »(exprω(), repr e), «expr * »(«expr ^ »(exprω(), (1 : ordinal.{0})), «expr ^ »(exprω(), «expr - »(repr e, 1))))] [],
    { have [] [] [":=", expr mt repr_inj.1 e0],
      rw ["[", "<-", expr power_add, ",", expr ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 this), "]"] [] },
    refine [expr ⟨NF.oadd (by apply_instance) _ _, _⟩],
    { simp [] [] [] [] [] ["at", ident this, "⊢"],
      refine [expr IH₁.below_of_lt' «expr $ »((mul_lt_mul_iff_left omega_pos).1, lt_of_le_of_lt (le_add_right _ m') _)],
      rw ["[", "<-", expr this, ",", "<-", expr IH₂, "]"] [],
      exact [expr h.snd'.repr_lt] },
    { rw [expr this] [],
      simp [] [] [] ["[", expr ordinal.mul_add, ",", expr mul_assoc, ",", expr add_assoc, "]"] [] [] } }
end

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem scale_eq_mul (x) [NF x] : ∀ (o) [NF o], «expr = »(scale x o, «expr * »(oadd x 1 0, o))
| 0, h := rfl
| oadd e n a, h := begin
  simp [] [] [] ["[", expr («expr * »), "]"] [] [],
  simp [] [] [] ["[", expr mul, ",", expr scale, "]"] [] [],
  haveI [] [] [":=", expr h.snd],
  by_cases [expr e0, ":", expr «expr = »(e, 0)],
  { rw [expr scale_eq_mul] [],
    simp [] [] [] ["[", expr e0, ",", expr h.zero_of_zero, ",", expr show «expr = »(«expr + »(x, 0), x), from repr_inj.1 (by simp [] [] [] [] [] []), "]"] [] [] },
  { simp [] [] [] ["[", expr e0, ",", expr scale_eq_mul, ",", expr («expr * »), "]"] [] [] }
end

instance NF_scale x [NF x] o [NF o] : NF (scale x o) :=
  by 
    rw [scale_eq_mul] <;> infer_instance

@[simp]
theorem repr_scale x [NF x] o [NF o] : reprₓ (scale x o) = (ω^reprₓ x)*reprₓ o :=
  by 
    simp [scale_eq_mul]

theorem NF_repr_split {o o' m} [NF o] (h : split o = (o', m)) : NF o' ∧ reprₓ o = reprₓ o'+m :=
  by 
    cases' e : split' o with a n 
    cases' NF_repr_split' e with s₁ s₂ 
    skip 
    rw [split_eq_scale_split' e] at h 
    injection h 
    substs o' n 
    simp [repr_scale, s₂.symm]
    infer_instance

theorem split_dvd {o o' m} [NF o] (h : split o = (o', m)) : ω ∣ reprₓ o' :=
  by 
    cases' e : split' o with a n 
    rw [split_eq_scale_split' e] at h 
    injection h 
    subst o' 
    cases NF_repr_split' e 
    skip 
    simp 

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem split_add_lt
{o e n a m}
[NF o]
(h : «expr = »(split o, (oadd e n a, m))) : «expr < »(«expr + »(repr a, m), «expr ^ »(exprω(), repr e)) :=
begin
  cases [expr NF_repr_split h] ["with", ident h₁, ident h₂],
  cases [expr h₁.of_dvd_omega (split_dvd h)] ["with", ident e0, ident d],
  have [] [] [":=", expr h₁.fst],
  have [] [] [":=", expr h₁.snd],
  refine [expr add_lt_omega_power h₁.snd'.repr_lt (lt_of_lt_of_le (nat_lt_omega _) _)],
  simpa [] [] [] [] [] ["using", expr power_le_power_right omega_pos (one_le_iff_ne_zero.2 e0)]
end

@[simp]
theorem mul_nat_eq_mul n o : mul_nat o n = o*of_nat n :=
  by 
    cases o <;> cases n <;> rfl

instance NF_mul_nat o [NF o] n : NF (mul_nat o n) :=
  by 
    simp  <;> infer_instance

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance NF_power_aux (e a0 a) [NF e] [NF a0] [NF a] : ∀ k m, NF (power_aux e a0 a k m)
| k, 0 := by cases [expr k] []; exact [expr NF.zero]
| 0, «expr + »(m, 1) := NF.oadd_zero _ _
| «expr + »(k, 1), «expr + »(m, 1) := by haveI [] [] [":=", expr NF_power_aux k]; simp [] [] [] ["[", expr power_aux, ",", expr nat.succ_ne_zero, "]"] [] []; apply_instance

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance NF_power (o₁ o₂) [NF o₁] [NF o₂] : NF «expr ^ »(o₁, o₂) :=
begin
  cases [expr e₁, ":", expr split o₁] ["with", ident a, ident m],
  have [ident na] [] [":=", expr (NF_repr_split e₁).1],
  cases [expr e₂, ":", expr split' o₂] ["with", ident b', ident k],
  haveI [] [] [":=", expr (NF_repr_split' e₂).1],
  casesI [expr a] ["with", ident a0, ident n, ident a'],
  { cases [expr m] ["with", ident m],
    { by_cases [expr «expr = »(o₂, 0)]; simp [] [] [] ["[", expr pow, ",", expr power, ",", "*", "]"] [] []; apply_instance },
    { by_cases [expr «expr = »(m, 0)],
      { simp [] [] ["only"] ["[", expr pow, ",", expr power, ",", "*", ",", expr zero_def, "]"] [] [],
        apply_instance },
      { simp [] [] [] ["[", expr pow, ",", expr power, ",", "*", ",", "-", ident npow_eq_pow, "]"] [] [],
        apply_instance } } },
  { simp [] [] [] ["[", expr pow, ",", expr power, ",", expr e₁, ",", expr e₂, ",", expr split_eq_scale_split' e₂, "]"] [] [],
    have [] [] [":=", expr na.fst],
    cases [expr k] ["with", ident k]; simp [] [] [] ["[", expr succ_eq_add_one, ",", expr power, "]"] [] []; resetI; apply_instance }
end

theorem scale_power_aux (e a0 a : Onote) [NF e] [NF a0] [NF a] :
  ∀ k m, reprₓ (power_aux e a0 a k m) = (ω^reprₓ e)*reprₓ (power_aux 0 a0 a k m)
| 0, m =>
  by 
    cases m <;> simp [power_aux]
| k+1, m =>
  by 
    byCases' m = 0 <;> simp [h, power_aux, Ordinal.mul_add, power_add, mul_assocₓ, scale_power_aux]

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem repr_power_aux₁
{e a}
[Ne : NF e]
[Na : NF a]
{a' : ordinal}
(e0 : «expr ≠ »(repr e, 0))
(h : «expr < »(a', «expr ^ »(exprω(), repr e)))
(aa : «expr = »(repr a, a'))
(n : «exprℕ+»()) : «expr = »(«expr ^ »(«expr + »(«expr * »(«expr ^ »(exprω(), repr e), (n : exprℕ())), a'), exprω()), «expr ^ »(«expr ^ »(exprω(), repr e), exprω())) :=
begin
  subst [expr aa],
  have [ident No] [] [":=", expr Ne.oadd n (Na.below_of_lt' h)],
  have [] [] [":=", expr omega_le_oadd e n a],
  unfold [ident repr] ["at", ident this],
  refine [expr le_antisymm _ (power_le_power_left _ this)],
  apply [expr (power_le_of_limit «expr $ »(ne_of_gt, lt_of_lt_of_le (power_pos _ omega_pos) this) omega_is_limit).2],
  intros [ident b, ident l],
  have [] [] [":=", expr (No.below_of_lt (lt_succ_self _)).repr_lt],
  unfold [ident repr] ["at", ident this],
  apply [expr le_trans «expr $ »(power_le_power_left b, le_of_lt this)],
  rw ["[", "<-", expr power_mul, ",", "<-", expr power_mul, "]"] [],
  apply [expr power_le_power_right omega_pos],
  cases [expr le_or_lt exprω() (repr e)] ["with", ident h, ident h],
  { apply [expr le_trans «expr $ »(mul_le_mul_left _, «expr $ »(le_of_lt, lt_succ_self _))],
    rw ["[", expr succ, ",", expr add_mul_succ _ (one_add_of_omega_le h), ",", "<-", expr succ, ",", expr succ_le, ",", expr mul_lt_mul_iff_left (ordinal.pos_iff_ne_zero.2 e0), "]"] [],
    exact [expr omega_is_limit.2 _ l] },
  { refine [expr le_trans «expr $ »(le_of_lt, mul_lt_omega (omega_is_limit.2 _ h) l) _],
    simpa [] [] [] [] [] ["using", expr mul_le_mul_right exprω() (one_le_iff_ne_zero.2 e0)] }
end

section 

local infixr:0 "^" => @pow Ordinal.{0} Ordinal Ordinal.hasPow

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem repr_power_aux₂
{a0 a'}
[N0 : NF a0]
[Na' : NF a']
(m : exprℕ())
(d : «expr ∣ »(exprω(), repr a'))
(e0 : «expr ≠ »(repr a0, 0))
(h : «expr < »(«expr + »(repr a', m), «expr ^ »(exprω(), repr a0)))
(n : «exprℕ+»())
(k : exprℕ()) : let R := repr (power_aux 0 a0 «expr * »(oadd a0 n a', of_nat m) k m) in
«expr ∧ »(«expr ≠ »(k, 0) → «expr < »(R, «expr ^ »(«expr ^ »(exprω(), repr a0), succ k)), «expr = »(«expr + »(«expr * »(«expr ^ »(«expr ^ »(exprω(), repr a0), k), «expr + »(«expr * »(«expr ^ »(exprω(), repr a0), (n : exprℕ())), repr a')), R), «expr ^ »(«expr + »(«expr + »(«expr * »(«expr ^ »(exprω(), repr a0), (n : exprℕ())), repr a'), m), succ k))) :=
begin
  intro [],
  haveI [ident No] [":", expr NF (oadd a0 n a')] [":=", expr N0.oadd n «expr $ »(Na'.below_of_lt', lt_of_le_of_lt (le_add_right _ _) h)],
  induction [expr k] [] ["with", ident k, ident IH] [],
  { cases [expr m] []; simp [] [] [] ["[", expr power_aux, ",", expr R, "]"] [] [] },
  rename [ident R, ident R'],
  let [ident R] [] [":=", expr repr (power_aux 0 a0 «expr * »(oadd a0 n a', of_nat m) k m)],
  let [ident ω0] [] [":=", expr «expr ^ »(exprω(), repr a0)],
  let [ident α'] [] [":=", expr «expr + »(«expr * »(ω0, n), repr a')],
  change [expr «expr ∧ »(«expr ≠ »(k, 0) → «expr < »(R, «expr ^ »(ω0, succ k)), «expr = »(«expr + »(«expr * »(«expr ^ »(ω0, k), α'), R), «expr ^ »(«expr + »(α', m), succ k)))] [] ["at", ident IH],
  have [ident RR] [":", expr «expr = »(R', «expr + »(«expr * »(«expr ^ »(ω0, k), «expr * »(α', m)), R))] [],
  { by_cases [expr «expr = »(m, 0)]; simp [] [] [] ["[", expr h, ",", expr R', ",", expr power_aux, ",", expr R, ",", expr power_mul, "]"] [] [],
    { cases [expr k] []; simp [] [] [] ["[", expr power_aux, "]"] [] [] },
    { refl } },
  have [ident α0] [":", expr «expr < »(0, α')] [],
  { simpa [] [] [] ["[", expr α', ",", expr lt_def, ",", expr repr, "]"] [] ["using", expr oadd_pos a0 n a'] },
  have [ident ω00] [":", expr «expr < »(0, «expr ^ »(ω0, k))] [":=", expr power_pos _ (power_pos _ omega_pos)],
  have [ident Rl] [":", expr «expr < »(R, «expr ^ »(exprω(), «expr * »(repr a0, succ «expr↑ »(k))))] [],
  { by_cases [expr k0, ":", expr «expr = »(k, 0)],
    { simp [] [] [] ["[", expr k0, "]"] [] [],
      refine [expr lt_of_lt_of_le _ (power_le_power_right omega_pos (one_le_iff_ne_zero.2 e0))],
      cases [expr m] ["with", ident m]; simp [] [] [] ["[", expr k0, ",", expr R, ",", expr power_aux, ",", expr omega_pos, "]"] [] [],
      rw ["[", "<-", expr nat.cast_succ, "]"] [],
      apply [expr nat_lt_omega] },
    { rw [expr power_mul] [],
      exact [expr IH.1 k0] } },
  refine [expr ⟨λ _, _, _⟩],
  { rw ["[", expr RR, ",", "<-", expr power_mul _ _ (succ k.succ), "]"] [],
    have [ident e0] [] [":=", expr ordinal.pos_iff_ne_zero.2 e0],
    have [ident rr0] [] [":=", expr lt_of_lt_of_le e0 (le_add_left _ _)],
    apply [expr add_lt_omega_power],
    { simp [] [] [] ["[", expr power_mul, ",", expr ω0, ",", expr power_add, ",", expr mul_assoc, "]"] [] [],
      rw ["[", expr mul_lt_mul_iff_left ω00, ",", "<-", expr ordinal.power_add, "]"] [],
      have [] [] [":=", expr (No.below_of_lt _).repr_lt],
      unfold [ident repr] ["at", ident this],
      refine [expr mul_lt_omega_power rr0 this (nat_lt_omega _)],
      simpa [] [] [] [] [] ["using", expr (add_lt_add_iff_left (repr a0)).2 e0] },
    { refine [expr lt_of_lt_of_le Rl «expr $ »(power_le_power_right omega_pos, «expr $ »(mul_le_mul_left _, «expr $ »(succ_le_succ.2, «expr $ »(nat_cast_le.2, le_of_lt k.lt_succ_self))))] } },
  calc
    «expr = »(«expr + »(«expr * »(«expr ^ »(ω0, k.succ), α'), R'), «expr + »(«expr * »(«expr ^ »(ω0, succ k), α'), «expr + »(«expr * »(«expr * »(«expr ^ »(ω0, k), α'), m), R))) : by rw ["[", expr nat_cast_succ, ",", expr RR, ",", "<-", expr mul_assoc, "]"] []
    «expr = »(..., «expr + »(«expr * »(«expr + »(«expr * »(«expr ^ »(ω0, k), α'), R), α'), «expr * »(«expr + »(«expr * »(«expr ^ »(ω0, k), α'), R), m))) : _
    «expr = »(..., «expr ^ »(«expr + »(α', m), succ k.succ)) : by rw ["[", "<-", expr ordinal.mul_add, ",", "<-", expr nat_cast_succ, ",", expr power_succ, ",", expr IH.2, "]"] [],
  congr' [1] [],
  { have [ident αd] [":", expr «expr ∣ »(exprω(), α')] [":=", expr dvd_add (dvd_mul_of_dvd_left (by simpa [] [] [] [] [] ["using", expr power_dvd_power exprω() (one_le_iff_ne_zero.2 e0)]) _) d],
    rw ["[", expr ordinal.mul_add «expr ^ »(ω0, k), ",", expr add_assoc, ",", "<-", expr mul_assoc, ",", "<-", expr power_succ, ",", expr add_mul_limit _ (is_limit_iff_omega_dvd.2 ⟨ne_of_gt α0, αd⟩), ",", expr mul_assoc, ",", expr @mul_omega_dvd n (nat_cast_pos.2 n.pos) (nat_lt_omega _) _ αd, "]"] [],
    apply [expr @add_absorp _ «expr * »(repr a0, succ k)],
    { refine [expr add_lt_omega_power _ Rl],
      rw ["[", expr power_mul, ",", expr power_succ, ",", expr mul_lt_mul_iff_left ω00, "]"] [],
      exact [expr No.snd'.repr_lt] },
    { have [] [] [":=", expr mul_le_mul_left «expr ^ »(ω0, succ k) «expr $ »(one_le_iff_pos.2, nat_cast_pos.2 n.pos)],
      rw [expr power_mul] [],
      simpa [] [] [] ["[", "-", ident power_succ, "]"] [] [] } },
  { cases [expr m] [],
    { have [] [":", expr «expr = »(R, 0)] [],
      { cases [expr k] []; simp [] [] [] ["[", expr R, ",", expr power_aux, "]"] [] [] },
      simp [] [] [] ["[", expr this, "]"] [] [] },
    { rw ["[", "<-", expr nat_cast_succ, ",", expr add_mul_succ, "]"] [],
      apply [expr add_absorp Rl],
      rw ["[", expr power_mul, ",", expr power_succ, "]"] [],
      apply [expr ordinal.mul_le_mul_left],
      simpa [] [] [] ["[", expr α', ",", expr repr, "]"] [] ["using", expr omega_le_oadd a0 n a'] } }
end

end 

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem repr_power (o₁ o₂) [NF o₁] [NF o₂] : «expr = »(repr «expr ^ »(o₁, o₂), «expr ^ »(repr o₁, repr o₂)) :=
begin
  cases [expr e₁, ":", expr split o₁] ["with", ident a, ident m],
  cases [expr NF_repr_split e₁] ["with", ident N₁, ident r₁],
  cases [expr a] ["with", ident a0, ident n, ident a'],
  { cases [expr m] ["with", ident m],
    { by_cases [expr «expr = »(o₂, 0)]; simp [] [] [] ["[", expr power_def, ",", expr power, ",", expr e₁, ",", expr h, ",", expr r₁, "]"] [] [],
      have [] [] [":=", expr mt repr_inj.1 h],
      rw [expr zero_power this] [] },
    { cases [expr e₂, ":", expr split' o₂] ["with", ident b', ident k],
      cases [expr NF_repr_split' e₂] ["with", "_", ident r₂],
      by_cases [expr «expr = »(m, 0)]; simp [] [] [] ["[", expr power_def, ",", expr power, ",", expr e₁, ",", expr h, ",", expr r₁, ",", expr e₂, ",", expr r₂, ",", "-", ident nat.cast_succ, "]"] [] [],
      rw ["[", expr power_add, ",", expr power_mul, ",", expr power_omega _ (nat_lt_omega _), "]"] [],
      simpa [] [] [] [] [] ["using", expr nat_cast_lt.2 «expr $ »(nat.succ_lt_succ, pos_iff_ne_zero.2 h)] } },
  { haveI [] [] [":=", expr N₁.fst],
    haveI [] [] [":=", expr N₁.snd],
    cases [expr N₁.of_dvd_omega (split_dvd e₁)] ["with", ident a00, ident ad],
    have [ident al] [] [":=", expr split_add_lt e₁],
    have [ident aa] [":", expr «expr = »(repr «expr + »(a', of_nat m), «expr + »(repr a', m))] [],
    { simp [] [] [] [] [] [] },
    cases [expr e₂, ":", expr split' o₂] ["with", ident b', ident k],
    cases [expr NF_repr_split' e₂] ["with", "_", ident r₂],
    simp [] [] [] ["[", expr power_def, ",", expr power, ",", expr e₁, ",", expr r₁, ",", expr split_eq_scale_split' e₂, "]"] [] [],
    cases [expr k] ["with", ident k]; resetI,
    { simp [] [] [] ["[", expr power, ",", expr r₂, ",", expr power_mul, ",", expr repr_power_aux₁ a00 al aa, ",", expr add_assoc, "]"] [] [] },
    { simp [] [] [] ["[", expr succ_eq_add_one, ",", expr power, ",", expr r₂, ",", expr power_add, ",", expr power_mul, ",", expr mul_assoc, ",", expr add_assoc, "]"] [] [],
      rw ["[", expr repr_power_aux₁ a00 al aa, ",", expr scale_power_aux, "]"] [],
      simp [] [] [] ["[", expr power_mul, "]"] [] [],
      rw ["[", "<-", expr ordinal.mul_add, ",", "<-", expr add_assoc «expr * »(«expr ^ »(exprω(), repr a0), (n : exprℕ())), "]"] [],
      congr' [1] [],
      rw ["[", "<-", expr power_succ, "]"] [],
      exact [expr (repr_power_aux₂ _ ad a00 al _ _).2] } }
end

end Onote

/-- The type of normal ordinal notations. (It would have been
  nicer to define this right in the inductive type, but `NF o`
  requires `repr` which requires `onote`, so all these things
  would have to be defined at once, which messes up the VM
  representation.) -/
def Nonote :=
  { o : Onote // o.NF }

instance : DecidableEq Nonote :=
  by 
    unfold Nonote <;> infer_instance

namespace Nonote

open Onote

instance NF (o : Nonote) : NF o.1 :=
  o.2

/-- Construct a `nonote` from an ordinal notation
  (and infer normality) -/
def mk (o : Onote) [h : NF o] : Nonote :=
  ⟨o, h⟩

/-- The ordinal represented by an ordinal notation.
  (This function is noncomputable because ordinal
  arithmetic is noncomputable. In computational applications
  `nonote` can be used exclusively without reference
  to `ordinal`, but this function allows for correctness
  results to be stated.) -/
noncomputable def reprₓ (o : Nonote) : Ordinal :=
  o.1.repr

instance : HasToString Nonote :=
  ⟨fun x => x.1.toString⟩

instance : HasRepr Nonote :=
  ⟨fun x => x.1.repr'⟩

instance : Preorderₓ Nonote :=
  { le := fun x y => reprₓ x ≤ reprₓ y, lt := fun x y => reprₓ x < reprₓ y, le_refl := fun a => @le_reflₓ Ordinal _ _,
    le_trans := fun a b c => @le_transₓ Ordinal _ _ _ _,
    lt_iff_le_not_le := fun a b => @lt_iff_le_not_leₓ Ordinal _ _ _ }

instance : HasZero Nonote :=
  ⟨⟨0, NF.zero⟩⟩

instance : Inhabited Nonote :=
  ⟨0⟩

theorem wf : @WellFounded Nonote (· < ·) :=
  InvImage.wfₓ reprₓ Ordinal.wf

instance : HasWellFounded Nonote :=
  ⟨· < ·, wf⟩

/-- Convert a natural number to an ordinal notation -/
def of_nat (n : ℕ) : Nonote :=
  ⟨of_nat n, ⟨⟨_, NF_below_of_nat _⟩⟩⟩

/-- Compare ordinal notations -/
def cmp (a b : Nonote) : Ordering :=
  cmp a.1 b.1

-- error in SetTheory.OrdinalNotation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cmp_compares : ∀ a b : nonote, (cmp a b).compares a b
| ⟨a, ha⟩, ⟨b, hb⟩ := begin
  resetI,
  dsimp [] ["[", expr cmp, "]"] [] [],
  have [] [] [":=", expr onote.cmp_compares a b],
  cases [expr onote.cmp a b] []; try { exact [expr this] },
  exact [expr subtype.mk_eq_mk.2 this]
end

instance : LinearOrderₓ Nonote :=
  linearOrderOfCompares cmp cmp_compares

instance : IsWellOrder Nonote (· < ·) :=
  ⟨wf⟩

/-- Asserts that `repr a < ω ^ repr b`. Used in `nonote.rec_on` -/
def below (a b : Nonote) : Prop :=
  NF_below a.1 (reprₓ b)

/-- The `oadd` pseudo-constructor for `nonote` -/
def oadd (e : Nonote) (n : ℕ+) (a : Nonote) (h : below a e) : Nonote :=
  ⟨_, NF.oadd e.2 n h⟩

/-- This is a recursor-like theorem for `nonote` suggesting an
  inductive definition, which can't actually be defined this
  way due to conflicting dependencies. -/
@[elab_as_eliminator]
def rec_on {C : Nonote → Sort _} (o : Nonote) (H0 : C 0) (H1 : ∀ e n a h, C e → C a → C (oadd e n a h)) : C o :=
  by 
    cases' o with o h 
    induction' o with e n a IHe IHa
    ·
      exact H0
    ·
      exact H1 ⟨e, h.fst⟩ n ⟨a, h.snd⟩ h.snd' (IHe _) (IHa _)

/-- Addition of ordinal notations -/
instance : Add Nonote :=
  ⟨fun x y => mk (x.1+y.1)⟩

theorem repr_add a b : reprₓ (a+b) = reprₓ a+reprₓ b :=
  Onote.repr_add a.1 b.1

/-- Subtraction of ordinal notations -/
instance : Sub Nonote :=
  ⟨fun x y => mk (x.1 - y.1)⟩

theorem repr_sub a b : reprₓ (a - b) = reprₓ a - reprₓ b :=
  Onote.repr_sub a.1 b.1

/-- Multiplication of ordinal notations -/
instance : Mul Nonote :=
  ⟨fun x y => mk (x.1*y.1)⟩

theorem repr_mul a b : reprₓ (a*b) = reprₓ a*reprₓ b :=
  Onote.repr_mul a.1 b.1

/-- Exponentiation of ordinal notations -/
def power (x y : Nonote) :=
  mk (x.1.power y.1)

theorem repr_power a b : reprₓ (power a b) = (reprₓ a).power (reprₓ b) :=
  Onote.repr_power a.1 b.1

end Nonote

