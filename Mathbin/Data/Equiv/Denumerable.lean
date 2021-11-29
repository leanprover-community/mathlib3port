import Mathbin.Data.Fintype.Basic 
import Mathbin.Data.Equiv.Encodable.Basic 
import Mathbin.Data.List.MinMax

/-!
# Denumerable types

This file defines denumerable (countably infinite) types as a typeclass extending `encodable`. This
is used to provide explicit encode/decode functions from and to `ℕ`, with the information that those
functions are inverses of each other.

## Implementation notes

This property already has a name, namely `α ≃ ℕ`, but here we are interested in using it as a
typeclass.
-/


/-- A denumerable type is (constructively) bijective with `ℕ`. Typeclass equivalent of `α ≃ ℕ`. -/
class Denumerable(α : Type _) extends Encodable α where 
  decode_inv : ∀ n, ∃ (a : _)(_ : a ∈ decode n), encode a = n

open Nat

namespace Denumerable

section 

variable{α : Type _}{β : Type _}[Denumerable α][Denumerable β]

open Encodable

theorem decode_is_some α [Denumerable α] (n : ℕ) : (decode α n).isSome :=
  Option.is_some_iff_exists.2$ (decode_inv n).imp$ fun a => Exists.fst

/-- Returns the `n`-th element of `α` indexed by the decoding. -/
def of_nat α [f : Denumerable α] (n : ℕ) : α :=
  Option.get (decode_is_some α n)

@[simp]
theorem decode_eq_of_nat α [Denumerable α] (n : ℕ) : decode α n = some (of_nat α n) :=
  Option.eq_some_of_is_some _

@[simp]
theorem of_nat_of_decode {n b} (h : decode α n = some b) : of_nat α n = b :=
  Option.some.injₓ$ (decode_eq_of_nat _ _).symm.trans h

@[simp]
theorem encode_of_nat n : encode (of_nat α n) = n :=
  let ⟨a, h, e⟩ := decode_inv n 
  by 
    rwa [of_nat_of_decode h]

@[simp]
theorem of_nat_encode a : of_nat α (encode a) = a :=
  of_nat_of_decode (encodek _)

/-- A denumerable type is equivalent to `ℕ`. -/
def eqv α [Denumerable α] : α ≃ ℕ :=
  ⟨encode, of_nat α, of_nat_encode, encode_of_nat⟩

instance (priority := 100) : Infinite α :=
  Infinite.of_surjective _ (eqv α).Surjective

/-- A type equivalent to `ℕ` is denumerable. -/
def mk' {α} (e : α ≃ ℕ) : Denumerable α :=
  { encode := e, decode := some ∘ e.symm, encodek := fun a => congr_argₓ some (e.symm_apply_apply _),
    decode_inv := fun n => ⟨_, rfl, e.apply_symm_apply _⟩ }

/-- Denumerability is conserved by equivalences. This is transitivity of equivalence the denumerable
way. -/
def of_equiv α {β} [Denumerable α] (e : β ≃ α) : Denumerable β :=
  { Encodable.ofEquiv _ e with
    decode_inv :=
      fun n =>
        by 
          simp  }

@[simp]
theorem of_equiv_of_nat α {β} [Denumerable α] (e : β ≃ α) n : @of_nat β (of_equiv _ e) n = e.symm (of_nat α n) :=
  by 
    apply of_nat_of_decode <;> show Option.map _ _ = _ <;> simp 

/-- All denumerable types are equivalent. -/
def equiv₂ α β [Denumerable α] [Denumerable β] : α ≃ β :=
  (eqv α).trans (eqv β).symm

instance Nat : Denumerable ℕ :=
  ⟨fun n => ⟨_, rfl, rfl⟩⟩

@[simp]
theorem of_nat_nat n : of_nat ℕ n = n :=
  rfl

/-- If `α` is denumerable, then so is `option α`. -/
instance Option : Denumerable (Option α) :=
  ⟨fun n =>
      by 
        cases n
        ·
          refine' ⟨none, _, encode_none⟩
          rw [decode_option_zero, Option.mem_def]
        refine' ⟨some (of_nat α n), _, _⟩
        ·
          rw [decode_option_succ, decode_eq_of_nat, Option.map_some', Option.mem_def]
        rw [encode_some, encode_of_nat]⟩

/-- If `α` and `β` are denumerable, then so is their sum. -/
instance Sum : Denumerable (Sum α β) :=
  ⟨fun n =>
      by 
        suffices  : ∃ (a : _)(_ : a ∈ @decode_sum α β _ _ n), encode_sum a = bit (bodd n) (div2 n)
        ·
          simpa [bit_decomp]
        simp [decode_sum] <;> cases bodd n <;> simp [decode_sum, bit, encode_sum]⟩

section Sigma

variable{γ : α → Type _}[∀ a, Denumerable (γ a)]

/-- A denumerable collection of denumerable types is denumerable. -/
instance Sigma : Denumerable (Sigma γ) :=
  ⟨fun n =>
      by 
        simp [decode_sigma] <;>
          exact
            ⟨_, _, ⟨rfl, HEq.rfl⟩,
              by 
                simp ⟩⟩

@[simp]
theorem sigma_of_nat_val (n : ℕ) : of_nat (Sigma γ) n = ⟨of_nat α (unpair n).1, of_nat (γ _) (unpair n).2⟩ :=
  Option.some.injₓ$
    by 
      rw [←decode_eq_of_nat, decode_sigma_val] <;> simp  <;> rfl

end Sigma

/-- If `α` and `β` are denumerable, then so is their product. -/
instance Prod : Denumerable (α × β) :=
  of_equiv _ (Equiv.sigmaEquivProd α β).symm

@[simp]
theorem prod_of_nat_val (n : ℕ) : of_nat (α × β) n = (of_nat α (unpair n).1, of_nat β (unpair n).2) :=
  by 
    simp  <;> rfl

@[simp]
theorem prod_nat_of_nat : of_nat (ℕ × ℕ) = unpair :=
  by 
    funext  <;> simp 

instance Int : Denumerable ℤ :=
  Denumerable.mk' Equiv.intEquivNat

instance Pnat : Denumerable ℕ+ :=
  Denumerable.mk' Equiv.pnatEquivNat

/-- The lift of a denumerable type is denumerable. -/
instance Ulift : Denumerable (Ulift α) :=
  of_equiv _ Equiv.ulift

/-- The lift of a denumerable type is denumerable. -/
instance Plift : Denumerable (Plift α) :=
  of_equiv _ Equiv.plift

/-- If `α` is denumerable, then `α × α` and `α` are equivalent. -/
def pair : α × α ≃ α :=
  equiv₂ _ _

end 

end Denumerable

namespace Nat.Subtype

open Function Encodable

/-! ### Subsets of `ℕ` -/


variable{s : Set ℕ}[Infinite s]

section Classical

open_locale Classical

-- error in Data.Equiv.Denumerable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem exists_succ (x : s) : «expr∃ , »((n), «expr ∈ »(«expr + »(«expr + »(«expr↑ »(x), n), 1), s)) :=
«expr $ »(classical.by_contradiction, λ
 h, have ∀
 (a : exprℕ())
 (ha : «expr ∈ »(a, s)), «expr < »(a, succ x), from λ
 a
 ha, lt_of_not_ge (λ
  hax, h ⟨«expr - »(a, «expr + »(x, 1)), by rwa ["[", expr add_right_comm, ",", expr add_tsub_cancel_of_le hax, "]"] []⟩),
 fintype.false ⟨(((multiset.range (succ x)).filter ((«expr ∈ » s))).pmap (λ
    (y : exprℕ())
    (hy : «expr ∈ »(y, s)), subtype.mk y hy) (by simp [] [] [] ["[", "-", ident multiset.range_succ, "]"] [] [])).to_finset, by simpa [] [] [] ["[", expr subtype.ext_iff_val, ",", expr multiset.mem_filter, ",", "-", ident multiset.range_succ, "]"] [] []⟩)

end Classical

variable[DecidablePred (· ∈ s)]

/-- Returns the next natural in a set, according to the usual ordering of `ℕ`. -/
def succ (x : s) : s :=
  have h : ∃ m, ((«expr↑ » x+m)+1) ∈ s := exists_succ x
  ⟨(«expr↑ » x+Nat.findₓ h)+1, Nat.find_specₓ h⟩

theorem succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
  have hx : ∃ m, ((«expr↑ » y+m)+1) ∈ s := exists_succ _ 
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h 
  have  : Nat.findₓ hx ≤ k := Nat.find_min'ₓ _ (hk ▸ x.2)
  show (((y : ℕ)+Nat.findₓ hx)+1) ≤ x by 
    rw [hk] <;> exact add_le_add_right (add_le_add_left this _) _

theorem le_succ_of_forall_lt_le {x y : s} (h : ∀ z (_ : z < x), z ≤ y) : x ≤ succ y :=
  have hx : ∃ m, ((«expr↑ » y+m)+1) ∈ s := exists_succ _ 
  show «expr↑ » x ≤ («expr↑ » y+Nat.findₓ hx)+1 from
    le_of_not_gtₓ$
      fun hxy =>
        (h ⟨_, Nat.find_specₓ hx⟩ hxy).not_lt$
          calc «expr↑ » y ≤ «expr↑ » y+Nat.findₓ hx := le_add_of_nonneg_right (Nat.zero_leₓ _)
            _ < («expr↑ » y+Nat.findₓ hx)+1 := Nat.lt_succ_selfₓ _
            

theorem lt_succ_self (x : s) : x < succ x :=
  calc (x : ℕ) ≤ x+_ := le_self_add 
    _ < succ x := Nat.lt_succ_selfₓ (x+_)
    

theorem lt_succ_iff_le {x y : s} : x < succ y ↔ x ≤ y :=
  ⟨fun h => le_of_not_gtₓ fun h' => not_le_of_gtₓ h (succ_le_of_lt h'), fun h => lt_of_le_of_ltₓ h (lt_succ_self _)⟩

/-- Returns the `n`-th element of a set, according to the usual ordering of `ℕ`. -/
def of_nat (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : ℕ → s
| 0 => ⊥
| n+1 => succ (of_nat n)

-- error in Data.Equiv.Denumerable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem of_nat_surjective_aux : ∀ {x : exprℕ()} (hx : «expr ∈ »(x, s)), «expr∃ , »((n), «expr = »(of_nat s n, ⟨x, hx⟩))
| x := λ
hx, let t : list s := ((list.range x).filter (λ
      y, «expr ∈ »(y, s))).pmap (λ (y : exprℕ()) (hy : «expr ∈ »(y, s)), ⟨y, hy⟩) (by simp [] [] [] [] [] []) in
have hmt : ∀
{y : s}, «expr ↔ »(«expr ∈ »(y, t), «expr < »(y, ⟨x, hx⟩)), by simp [] [] [] ["[", expr list.mem_filter, ",", expr subtype.ext_iff_val, ",", expr t, "]"] [] []; intros []; refl,
have wf : ∀
m : s, «expr = »(list.maximum t, m) → «expr < »(«expr↑ »(m), x), from λ
m hmax, by simpa [] [] [] ["[", expr hmt, "]"] [] ["using", expr list.maximum_mem hmax],
begin
  cases [expr hmax, ":", expr list.maximum t] ["with", ident m],
  { exact [expr ⟨0, le_antisymm bot_le (le_of_not_gt (λ
        h, «expr $ »(list.not_mem_nil («expr⊥»() : s), by rw ["[", "<-", expr list.maximum_eq_none.1 hmax, ",", expr hmt, "]"] []; exact [expr h])))⟩] },
  cases [expr of_nat_surjective_aux m.2] ["with", ident a, ident ha],
  exact [expr ⟨«expr + »(a, 1), «expr $ »(le_antisymm (by rw [expr of_nat] []; exact [expr succ_le_of_lt (by rw [expr ha] []; exact [expr wf _ hmax])]), by rw [expr of_nat] []; exact [expr le_succ_of_forall_lt_le (λ
       z hz, by rw [expr ha] []; cases [expr m] []; exact [expr list.le_maximum_of_mem (hmt.2 hz) hmax])])⟩]
end

theorem of_nat_surjective : surjective (of_nat s) :=
  fun ⟨x, hx⟩ => of_nat_surjective_aux hx

private def to_fun_aux (x : s) : ℕ :=
  (List.range x).countp (· ∈ s)

private theorem to_fun_aux_eq (x : s) : to_fun_aux x = ((Finset.range x).filter (· ∈ s)).card :=
  by 
    rw [to_fun_aux, List.countp_eq_length_filter] <;> rfl

open Finset

private theorem right_inverse_aux : ∀ n, to_fun_aux (of_nat s n) = n
| 0 =>
  by 
    rw [to_fun_aux_eq, card_eq_zero, eq_empty_iff_forall_not_mem]
    rintro n hn 
    rw [mem_filter, of_nat, mem_range] at hn 
    exact bot_le.not_lt (show (⟨n, hn.2⟩ : s) < ⊥ from hn.1)
| n+1 =>
  have ih : to_fun_aux (of_nat s n) = n := right_inverse_aux n 
  have h₁ : (of_nat s n : ℕ) ∉ (range (of_nat s n)).filter (· ∈ s) :=
    by 
      simp 
  have h₂ : (range (succ (of_nat s n))).filter (· ∈ s) = insert (of_nat s n) ((range (of_nat s n)).filter (· ∈ s)) :=
    by 
      simp only [Finset.ext_iff, mem_insert, mem_range, mem_filter]
      exact
        fun m =>
          ⟨fun h =>
              by 
                simp only [h.2, and_trueₓ] <;>
                  exact Or.symm (lt_or_eq_of_leₓ ((@lt_succ_iff_le _ _ _ ⟨m, h.2⟩ _).1 h.1)),
            fun h =>
              h.elim (fun h => h.symm ▸ ⟨lt_succ_self _, (of_nat s n).Prop⟩) fun h => ⟨h.1.trans (lt_succ_self _), h.2⟩⟩
  by 
    simp only [to_fun_aux_eq, of_nat, range_succ] at ih⊢
    conv  => toRHS rw [←ih, ←card_insert_of_not_mem h₁, ←h₂]

/-- Any infinite set of naturals is denumerable. -/
def Denumerable (s : Set ℕ) [DecidablePred (· ∈ s)] [Infinite s] : Denumerable s :=
  Denumerable.ofEquiv ℕ
    { toFun := to_fun_aux, invFun := of_nat s,
      left_inv := left_inverse_of_surjective_of_right_inverse of_nat_surjective right_inverse_aux,
      right_inv := right_inverse_aux }

end Nat.Subtype

namespace Denumerable

open Encodable

-- error in Data.Equiv.Denumerable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An infinite encodable type is denumerable. -/
def of_encodable_of_infinite (α : Type*) [encodable α] [infinite α] : denumerable α :=
begin
  letI [] [] [":=", expr @decidable_range_encode α _]; letI [] [":", expr infinite (set.range (@encode α _))] [":=", expr infinite.of_injective _ (equiv.of_injective _ encode_injective).injective],
  letI [] [] [":=", expr nat.subtype.denumerable (set.range (@encode α _))],
  exact [expr denumerable.of_equiv (set.range (@encode α _)) (equiv_range_encode α)]
end

end Denumerable

