import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Num.Lemmas
import Mathbin.Tactic.DeriveFintype

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_bool`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_bool`  : an encoding of bool.
-/


namespace Computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure encoding (α : Type) where
  Γ : Type
  encode : α → List Γ
  decode : List Γ → Option α
  decode_encode : ∀ x, decode (encode x) = some x

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure fin_encoding (α : Type) extends encoding α where
  ΓFin : Fintype Γ

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype

instance inhabited_Γ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩

/-- The natural inclusion of bool in Γ'. -/
def inclusion_bool_Γ' : Bool → Γ' :=
  Γ'.bit

/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def section_Γ'_bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => arbitraryₓ Bool

theorem left_inverse_section_inclusion : Function.LeftInverse section_Γ'_bool inclusion_bool_Γ' := fun x =>
  Bool.casesOn x rfl rfl

theorem inclusion_bool_Γ'_injective : Function.Injective inclusion_bool_Γ' :=
  Function.HasLeftInverse.injective (Exists.intro section_Γ'_bool left_inverse_section_inclusion)

/-- An encoding function of the positive binary numbers in bool. -/
def encode_pos_num : PosNum → List Bool
  | PosNum.one => [tt]
  | PosNum.bit0 n => ff :: encode_pos_num n
  | PosNum.bit1 n => tt :: encode_pos_num n

/-- An encoding function of the binary numbers in bool. -/
def encode_num : Num → List Bool
  | Num.zero => []
  | Num.pos n => encode_pos_num n

/-- An encoding function of ℕ in bool. -/
def encode_nat (n : ℕ) : List Bool :=
  encode_num n

/-- A decoding function from `list bool` to the positive binary numbers. -/
def decode_pos_num : List Bool → PosNum
  | ff :: l => PosNum.bit0 (decode_pos_num l)
  | tt :: l => ite (l = []) PosNum.one (PosNum.bit1 (decode_pos_num l))
  | _ => PosNum.one

/-- A decoding function from `list bool` to the binary numbers. -/
def decode_num : List Bool → Num := fun l => ite (l = []) Num.zero $ decode_pos_num l

/-- A decoding function from `list bool` to ℕ. -/
def decode_nat : List Bool → Nat := fun l => decode_num l

theorem encode_pos_num_nonempty (n : PosNum) : encode_pos_num n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun m => List.cons_ne_nil _ _) fun m => List.cons_ne_nil _ _

theorem decode_encode_pos_num : ∀ n, decode_pos_num (encode_pos_num n) = n := by
  intro n
  induction' n with m hm m hm <;> unfold encode_pos_num decode_pos_num
  · rfl
    
  · rw [hm]
    exact if_neg (encode_pos_num_nonempty m)
    
  · exact congr_argₓ PosNum.bit0 hm
    

theorem decode_encode_num : ∀ n, decode_num (encode_num n) = n := by
  intro n
  cases n <;> unfold encode_num decode_num
  · rfl
    
  rw [decode_encode_pos_num n]
  rw [PosNum.cast_to_num]
  exact if_neg (encode_pos_num_nonempty n)

theorem decode_encode_nat : ∀ n, decode_nat (encode_nat n) = n := by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_argₓ coeₓ (decode_encode_num (↑n))

/-- A binary encoding of ℕ in bool. -/
def encoding_nat_bool : encoding ℕ where
  Γ := Bool
  encode := encode_nat
  decode := fun n => some (decode_nat n)
  decode_encode := fun n => congr_argₓ _ (decode_encode_nat n)

/-- A binary fin_encoding of ℕ in bool. -/
def fin_encoding_nat_bool : fin_encoding ℕ :=
  ⟨encoding_nat_bool, Bool.fintype⟩

/-- A binary encoding of ℕ in Γ'. -/
def encoding_nat_Γ' : encoding ℕ where
  Γ := Γ'
  encode := fun x => List.map inclusion_bool_Γ' (encode_nat x)
  decode := fun x => some (decode_nat (List.map section_Γ'_bool x))
  decode_encode := fun x =>
    congr_argₓ _ $ by
      rw [List.map_mapₓ, List.map_id' left_inverse_section_inclusion, decode_encode_nat]

/-- A binary fin_encoding of ℕ in Γ'. -/
def fin_encoding_nat_Γ' : fin_encoding ℕ :=
  ⟨encoding_nat_Γ', Γ'.fintype⟩

/-- A unary encoding function of ℕ in bool. -/
def unary_encode_nat : Nat → List Bool
  | 0 => []
  | n + 1 => tt :: unary_encode_nat n

/-- A unary decoding function from `list bool` to ℕ. -/
def unary_decode_nat : List Bool → Nat :=
  List.length

theorem unary_decode_encode_nat : ∀ n, unary_decode_nat (unary_encode_nat n) = n := fun n =>
  Nat.rec rfl (fun m : ℕ hm => (congr_argₓ Nat.succ hm.symm).symm) n

/-- A unary fin_encoding of ℕ. -/
def unary_fin_encoding_nat : fin_encoding ℕ where
  Γ := Bool
  encode := unary_encode_nat
  decode := fun n => some (unary_decode_nat n)
  decode_encode := fun n => congr_argₓ _ (unary_decode_encode_nat n)
  ΓFin := Bool.fintype

/-- An encoding function of bool in bool. -/
def encode_bool : Bool → List Bool :=
  List.ret

/-- A decoding function from `list bool` to bool. -/
def decode_bool : List Bool → Bool
  | b :: _ => b
  | _ => arbitraryₓ Bool

theorem decode_encode_bool : ∀ b, decode_bool (encode_bool b) = b := fun b => Bool.casesOn b rfl rfl

/-- A fin_encoding of bool in bool. -/
def fin_encoding_bool_bool : fin_encoding Bool where
  Γ := Bool
  encode := encode_bool
  decode := fun x => some (decode_bool x)
  decode_encode := fun x => congr_argₓ _ (decode_encode_bool x)
  ΓFin := Bool.fintype

instance inhabited_fin_encoding : Inhabited (fin_encoding Bool) :=
  ⟨fin_encoding_bool_bool⟩

instance inhabited_encoding : Inhabited (encoding Bool) :=
  ⟨fin_encoding_bool_bool.toEncoding⟩

end Computability

