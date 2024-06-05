/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Smt.Util.Mathlib.Init
import Smt.Util.Mathlib.Algebra
import Smt.Util.Mathlib.Covariant



namespace Smt



section lemmas
variable
  {α : Type u}
  [Zero α] [One α]
  [PartialOrder α]
  [NZ : NeZero (1 : α)] [ZLE : ZeroLE (1 : α)]

@[simp]
theorem zero_lt_one : (0 : α) < 1 := by
  simp [lt_of_le_ne ZLE.out zero_ne_one]

variable (α)

theorem zero_lt_one' : (0 : α) < 1 :=
  zero_lt_one
end lemmas



class AddZeroClass (α : Type u) extends Zero α, Add α where
  protected zero_add : ∀ a : α, 0 + a = a
  protected add_zero : ∀ a : α, a + 0 = a

section lemmas
variable [AddZeroClass α]

@[simp]
theorem add_zero : ∀ a : α, a + 0 = a :=
  AddZeroClass.add_zero

@[simp]
theorem zero_add : ∀ a : α, 0 + a = a :=
  AddZeroClass.zero_add

theorem lt_add_of_pos_right
  [LT α]
  [CovariantClass α α (· + ·) (· < ·)]
  (a : α) {b : α} (h : 0 < b)
: a < a + b := by
  calc
    a = a + 0 := (add_zero a).symm
    _ < a + b := add_lt_add_left h a

theorem lt_add_of_lt_of_pos [Preorder α]
  [CovariantClass α α (· + ·) (· < ·)]
  {a b c : α} (hbc : b < c) (ha : 0 < a)
: b < c + a := by
  calc
    b < c := hbc
    _ = c + 0 := (add_zero c).symm
    _ < c + a := add_lt_add_left ha c

theorem lt_add_of_lt_of_nonneg
  [Preorder α]
  [CovariantClass α α (· + ·) (· ≤ ·)]
  {a b c : α} (hbc : b < c) (ha : 0 ≤ a)
: b < c + a := by
  calc
    b < c := hbc
    _ = c + 0 := (add_zero c).symm
    _ ≤ c + a := add_le_add_left ha c

theorem lt_add_of_lt_of_pos'
  [Preorder α]
  [CovariantClass α α (· + ·) (· ≤ ·)]
  {a b c : α} (hbc : b < c) (ha : 0 < a)
: b < c + a :=
  lt_add_of_lt_of_nonneg hbc (le_of_lt ha)

theorem Left.add_pos
  [Preorder α]
  [CovariantClass α α (· + ·) (· < ·)]
  {a b : α} (ha : 0 < a) (hb : 0 < b)
: 0 < a + b :=
  lt_add_of_lt_of_pos ha hb

theorem Left.add_pos'
  [Preorder α]
  [CovariantClass α α (· + ·) (· ≤ ·)]
  {a b : α} (ha : 0 < a) (hb : 0 < b)
: 0 < a + b :=
  lt_add_of_lt_of_pos' ha hb

theorem le_add_of_nonneg_right
  [LE α] [CovariantClass α α (· + ·) (· ≤ ·)]
  {a b : α} (h : 0 ≤ b)
: a ≤ a + b :=
  calc
    a = a + 0 := (add_zero a).symm
    _ ≤ a + b := add_le_add_left h a
end lemmas

namespace AddZeroClass
variable [Self : AddZeroClass α]
-- instance instAdd (priority := 50) [AddZeroClass α] : Add α :=
--   AddZeroClass.toAdd

end AddZeroClass



class MulZeroClass (α : Type u) extends Zero α, Mul α where
  protected zero_mul : ∀ a : α, 0 * a = 0
  protected mul_zero : ∀ a : α, a * 0 = 0

section lemmas
variable [MulZeroClass α]

theorem mul_zero : ∀ a : α, a * 0 = 0 :=
  MulZeroClass.mul_zero

theorem zero_mul : ∀ a : α, 0 * a = 0 :=
  MulZeroClass.zero_mul
end lemmas



class MulOneClass (α : Type u) extends One α, Mul α where
  protected one_mul : ∀ a : α, 1 * a = a
  protected mul_one : ∀ a : α, a * 1 = a

namespace MulOneClass
-- instance instMul (priority := 50) [MulOneClass α] : Mul α :=
--   MulOneClass.toMul
end MulOneClass

section lemmas
variable [MulOneClass α]

theorem mul_one : ∀ a : α, a * 1 = a :=
  MulOneClass.mul_one

theorem one_mul : ∀ a : α, 1 * a = a :=
  MulOneClass.one_mul
end lemmas



class MulZeroOneClass (α : Type u) extends MulZeroClass α, MulOneClass α



class Distrib (α : Type u) extends Add α, Mul α where
  protected left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c

section lemmas
variable [Distrib α]

theorem left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c :=
  Distrib.left_distrib

theorem right_distrib [Distrib α] : ∀ a b c : α, (a + b) * c = a * c + b * c :=
  Distrib.right_distrib
end lemmas



class AddCommMagma (α : Type u) extends Add α where
  protected add_comm : ∀ a b : α, a + b = b + a

section lemmas
variable [AddCommMagma α]

theorem add_comm : ∀ a b : α, a + b = b + a :=
  AddCommMagma.add_comm
end lemmas


class Semigroup (α : Type u) extends Mul α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)

section lemmas
variable [Semigroup α]

theorem mul_assoc : ∀ a b c : α, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc
end lemmas



class SemigroupWithZero (α : Type u) extends Semigroup α, MulZeroClass α



class AddSemigroup (α : Type u) extends Add α where
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

section lemmas
variable [AddSemigroup α]

theorem add_assoc : ∀ a b c : α, a + b + c = a + (b + c) :=
  AddSemigroup.add_assoc

-- instance (priority := 50) : Add α :=
--   AddSemigroup.toAdd
end lemmas



class AddCommSemigroup (α : Type u) extends AddSemigroup α, AddCommMagma α



class AddMonoid (α : Type u) extends AddSemigroup α, AddZeroClass α where
  protected nsmul : Nat → α → α
  protected nsmul_zero : ∀ a : α, nsmul 0 a = 0 :=
    by intros ; simp
  protected nsmul_succ : ∀ (n : Nat) (a : α), nsmul n.succ a = nsmul n a + a :=
    by intros ; simp

namespace AddMonoid
variable [Self : AddMonoid α]

instance instHMulNat : HMul Nat α α where
  hMul n a := Self.nsmul n a

theorem hmul_is_nsmul : (n : Nat) * a = Self.nsmul n a := rfl
end AddMonoid



class AddMonoidWithOne (α : Type u) extends NatCast α, AddMonoid α, One α where
  natCast := Nat.unaryCast
  natCast_zero : natCast 0 = 0 := by intros ; simp
  natCast_succ : ∀ n : Nat, natCast n.succ = natCast n + 1 := by intros ; simp

namespace AddMonoidWithOne
variable [Self : AddMonoidWithOne α]

instance instHAddNat : HAdd Nat α α where
  hAdd n a := (Self.natCast n) + a
end AddMonoidWithOne

section lemmas
variable [Self : AddMonoidWithOne α]

def natCast : Nat → α := Self.natCast
theorem natCast_zero : Self.natCast 0 = 0 := Self.natCast_zero
theorem natCast_succ : ∀ n : Nat, Self.natCast n.succ = Self.natCast n + 1 :=
  Self.natCast_succ

-- abbrev Nat.cast := @natCast
-- abbrev Nat.cast_zero := @natCast_zero
-- abbrev Nat.cast_succ := @natCast_succ

theorem nsmul_one (n : Nat) : n * (1 : α) = n := by
  induction n with
  | zero =>
    simp [AddMonoid.hmul_is_nsmul, Self.nsmul_zero, natCast_zero]
  | succ n ih =>
    rw [AddMonoid.hmul_is_nsmul, Self.nsmul_succ, ← AddMonoid.hmul_is_nsmul, ih]
    simp [natCast_succ]

theorem mono_cast
  [P : PartialOrder α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Z : ZeroLE (1 : α)]
: ∀ ⦃a b : Nat⦄, a ≤ b → (a : α) ≤ (b : α) := by
    intro a b hab
    induction hab
    case refl => exact P.le_refl _
    case step b h ih =>
      simp [natCast_succ]
      apply P.le_trans ↑a _ _ ih
      apply le_add_of_nonneg_right
      exact Z.out
end lemmas



class AddCommMonoid (α : Type u) extends AddMonoid α, AddCommSemigroup α



class AddCommMonoidWithOne (α : Type u) extends AddMonoidWithOne α, AddCommMonoid α


class Monoid (α : Type u) extends Semigroup α, MulOneClass α where
  /-- Raising to the power of a natural number. -/
  protected npow : Nat → α → α := Nat.npowRec
  /-- Raising to the power `(0 : Nat)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 :=
    by intros ; rfl
  /-- Raising to the power `(n + 1 : Nat)` behaves as expected. -/
  protected npow_succ : ∀ (n : Nat) (x : α), npow (n + 1) x = npow n x * x :=
    by intros ; simp



class MonoidWithZero (α : Type u) extends Monoid α, MulZeroOneClass α, SemigroupWithZero α



def SubNegMonoid.sub' {α : Type u} [AddMonoid α] [Neg α] (a b : α) : α := a + -b

class SubNegMonoid (α : Type u) extends AddMonoid α, Neg α, Sub α where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : α, a - b = a + -b :=
    by intros ; simp
  protected zsmul : Int → α → α
  protected zsmul_zero' : ∀ a : α, zsmul 0 a = 0 :=
    by intros ; simp
  protected zsmul_succ' (n : Nat) (a : α) :
    zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a
  := by intros ; simp
  protected zsmul_neg' (n : Nat) (a : α) :
    zsmul (Int.negSucc n) a = -zsmul n.succ a
  := by intros ; simp

namespace SubNegMonoid
variable [SubNegMonoid α]
end SubNegMonoid

section lemmas
variable [Self : SubNegMonoid α]

theorem sub_eq_add_neg : ∀ a b : α, a - b = a + -b :=
  Self.sub_eq_add_neg
end lemmas



class InvolutiveNeg (α : Type u) extends Neg α where
  protected neg_neg : ∀ x : α, - -x = x

section lemmas
variable [InvolutiveNeg α]

theorem neg_neg : ∀ x : α, - -x = x :=
  InvolutiveNeg.neg_neg
end lemmas



class AddGroup (α : Type u) extends SubNegMonoid α where
  protected add_left_neg : ∀ a : α, -a + a = 0

section lemmas
variable [AddGroup α]

theorem add_left_neg : ∀ a : α, -a + a = 0 :=
  AddGroup.add_left_neg

instance (priority := 100) AddGroup.covconv [I : CovariantClass α α (· + ·) r]
: ContravariantClass α α (· + ·) r where
  elim := by
    let ⟨coelim⟩ := I
    intro a b c ; simp
    intro h_r
    let h := coelim (-a) h_r
    simp at h
    rw [← add_assoc, ← add_assoc] at h
    simp [add_left_neg, zero_add] at h
    assumption

theorem left_neg_eq_right_neg {a b c : α} (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]

private
theorem neg_eq_of_add {a b : α} (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (add_left_neg a) h

instance AddGroup.instInvolutiveNeg : InvolutiveNeg α where
  neg_neg a := by
    apply neg_eq_of_add
    exact add_left_neg a

theorem add_right_neg (a : α) : a + -a = 0 :=
  by rw [← add_left_neg (-a), neg_eq_of_add (add_left_neg a)]

instance (priority := 100) AddGroup.covconv_swap [I : CovariantClass α α (swap (· + ·)) r]
: ContravariantClass α α (swap (· + ·)) r where
  elim := by
    let ⟨coelim⟩ := I
    intro a b c ; unfold swap ; simp
    intro h_r
    let h := coelim (-a) h_r
    unfold swap at h ; simp at h
    simp [add_assoc, add_right_neg, add_zero] at h
    assumption



theorem neg_le
  [LE α]
  [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [CovariantClass α α (swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  {a b : α}
: -a ≤ b ↔ -b ≤ a := by
  rw [← add_le_add_iff_right a]
  rw [← add_le_add_iff_left (-b)]
  simp only [add_left_neg, add_zero, ← add_assoc, zero_add]

theorem le_neg
  [LE α]
  [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [CovariantClass α α (swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  {a b : α}
: a ≤ -b ↔ b ≤ -a := by
  rw [← add_le_add_iff_left (-a)]
  rw [← add_le_add_iff_right b]
  simp only [add_left_neg, add_zero, add_assoc, zero_add]

theorem neg_lt_neg_iff
  [LT α]
  [CovariantClass α α (· + ·) (· < ·)]
  [CovariantClass α α (swap (· + ·)) (· < ·)]
  {a b : α}
: -a < -b ↔ b < a := by
  rw [← add_lt_add_iff_left a]
  rw [← add_lt_add_iff_right b]
  simp only [add_right_neg, add_assoc, add_left_neg, add_zero, zero_add]

theorem neg_lt
  [LT α]
  [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x < x_1]
  [CovariantClass α α (swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x < x_1]
  {a b : α}
: -a < b ↔ -b < a := by
  rw [← neg_lt_neg_iff, neg_neg]

theorem Left.neg_nonpos_iff
  [LE α]
  [CovariantClass α α (· + ·) (· ≤ ·)]
  {a : α}
: -a ≤ 0 ↔ 0 ≤ a := by
  rw [← add_le_add_iff_left a]
  simp [add_right_neg, add_zero]

theorem neg_add_cancel_left (a b : α) : (- a) + (a + b) = b :=
  by rw [←add_assoc, add_left_neg, zero_add]

theorem neg_add_cancel_right (a b : α) : a + (-b) + b = a :=
  by rw [add_assoc, add_left_neg, add_zero]

theorem sub_nonneg
  [LE α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)]
  {a b : α}
: 0 ≤ a - b ↔ b ≤ a := by
  rw [← add_le_add_iff_right b, zero_add, sub_eq_add_neg, neg_add_cancel_right]

theorem eq_sub_of_add_eq {a b c : α} (h : a + c = b) : a = b - c := by
  simp [← h, Nat.add_sub_cancel_right, sub_eq_add_neg, add_assoc, add_right_neg, add_zero]

theorem add_neg_cancel_left (a b : α) : a + (-a + b) = b :=
  by rw [← add_assoc, add_right_neg, zero_add]

theorem add_neg_cancel_right (a b : α) : a + b + -b = a :=
  by rw [add_assoc, add_right_neg, add_zero]

theorem add_neg_eq_iff_eq_add {a b c : α} : a + -b = c ↔ a = c + b := ⟨
  fun h ↦ by rw [← h, neg_add_cancel_right],
  fun h ↦ by rw [h, add_neg_cancel_right]
⟩

theorem sub_eq_iff_eq_add {a b c : α} : a - b = c ↔ a = c + b := by
  rw [sub_eq_add_neg, add_neg_eq_iff_eq_add]

theorem eq_neg_add_iff_add_eq {a b c : α} : a = -b + c ↔ b + a = c := ⟨
  fun h ↦ by rw [h, add_neg_cancel_left],
  fun h ↦ by rw [← h, neg_add_cancel_left]
⟩
end lemmas



class AddCommGroup (α : Type u) extends AddGroup α, AddCommMonoid α

namespace AddCommGroup
variable [Self : AddCommGroup α]
end AddCommGroup



class AddGroupWithOne (α : Type u) extends IntCast α, AddMonoidWithOne α, AddGroup α where
  /-- The canonical homomorphism `Int → α`. -/
  intCast := Int.castDef
  /-- The canonical homomorphism `Int → α` agrees with the one from `Nat → α` on `Nat`. -/
  intCast_ofNat : ∀ n : Nat, intCast (n : Nat) = Nat.cast n := by intros ; simp
  /-- The canonical homomorphism `Int → α` for negative values is just the negation of the values of
    the canonical homomorphism `Nat → α`. -/
  intCast_negSucc : ∀ n : Nat, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros ; simp



class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  /-- Addition is monotone in an ordered additive commutative group. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b



class SubtractionMonoid (α : Type u) extends SubNegMonoid α, InvolutiveNeg α where
  protected neg_add_rev (a b : α) : -(a + b) = -b + -a
  protected neg_eq_of_add (a b : α) : a + b = 0 → -a = b

section lemmas

instance AddGroupWithOne.instSubtractionMonoid [Self : AddGroupWithOne α]: SubtractionMonoid α where
  neg_neg a := by
    let i := (inferInstance : InvolutiveNeg α)
    apply i.neg_neg
  neg_add_rev := by
    intro a b
    rw [
      ← add_zero (-b + -a),
      ← add_right_neg (a + b),
      add_assoc (-b),
      ← add_assoc (-a),
      ← add_assoc (-a)
    ]
    simp only [add_left_neg, zero_add]
    rw [← add_assoc (-b)]
    simp only [add_left_neg, zero_add]
  neg_eq_of_add a b := Smt.neg_eq_of_add

variable [SubtractionMonoid α]
  {a b : α}

theorem neg_eq_of_add_eq_zero_right : a + b = 0 → -a = b :=
  SubtractionMonoid.neg_eq_of_add a b

theorem neg_eq_of_add_eq_zero_left (h : a + b = 0) : -b = a := by
  rw [← neg_eq_of_add_eq_zero_right h, neg_neg]

theorem eq_neg_of_add_eq_zero_left (h : a + b = 0) : a = -b := by
  rw [← neg_eq_of_add_eq_zero_left h]

@[simp]
theorem neg_add_rev (a b : α) : -(a + b) = -b + -a :=
  SubtractionMonoid.neg_add_rev _ _

@[simp]
theorem neg_sub : -(a - b) = b - a := by
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
end lemmas



class OrderedAddCommMonoid (α : Type u) extends AddCommMonoid α, PartialOrder α where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

namespace OrderedAddCommMonoid
variable [Self : OrderedAddCommMonoid α]

theorem zero_nsmul (a : α) : (0 : Nat) * a = 0 :=
  Self.nsmul_zero a

theorem zero_mul (a : α) : 0 * a = 0 :=
  Self.nsmul_zero a

theorem mul_zero (a : α) : 0 * a = 0 :=
  Self.nsmul_zero a

theorem succ_mul {n : Nat} (a : α) : (n + 1) * a = n * a + a :=
  Self.nsmul_succ n a

theorem succ_mul' {n : Nat} (a : α) : (n + 1) * a = a + n * a := by
  conv =>
    rhs
    rw [Self.add_comm]
  exact succ_mul a

theorem mul_pos
  [I : CovariantClass α α (· + ·) (· < ·)]
  {k : Nat} (a : α) (ha : 0 < a) (hk : k ≠ 0 := by simp)
: 0 < k * a := by
  rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨l, rfl⟩
  clear hk
  induction l with
  | zero =>
    rw [succ_mul, zero_mul, zero_add]
    assumption
  | succ l IH =>
    rw [succ_mul]
    exact Left.add_pos IH ha

theorem mul_pos'
  [CovariantClass α α (· + ·) (· ≤ ·)]
  {k : Nat} (a : α) (ha : 0 < a) (hk : k ≠ 0)
: 0 < k * a := by
  rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨l, rfl⟩
  clear hk
  induction l with
  | zero =>
    rw [succ_mul, zero_mul, zero_add]
    assumption
  | succ l IH =>
    rw [succ_mul]
    exact Left.add_pos' IH ha
end OrderedAddCommMonoid




class NonUnitalNonAssocSemiring (α : Type u)
extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u)
extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u)
extends NonUnitalNonAssocSemiring α, MulZeroOneClass α, AddCommMonoidWithOne α

class Semiring (α : Type u)
extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α



class HasDistribNeg (α : Type u) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section lemmas

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _
end lemmas



class Ring (α : Type u) extends Semiring α, AddCommGroup α, AddGroupWithOne α



class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

section lemmas
variable [NonUnitalNonAssocRing α]

-- instance : SubtractionMonoid α where
--   neg_neg := neg_neg
--   neg_add_rev a b := by
--     sorry
--   neg_eq_of_add a b := by
--     sorry

-- instance (priority := 100) : HasDistribNeg α where
--   neg := Neg.neg
--   neg_neg := neg_neg
--   neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, add_left_neg, zero_mul]
--   mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, add_left_neg, mul_zero]
end lemmas



class Nontrivial (α : Type u) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y



class StrictOrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α, Nontrivial α where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of two positive elements is positive. -/
  protected mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

namespace StrictOrderedRing
variable {α : Type u} [Self : StrictOrderedRing α]

instance instZeroLEOne : ZeroLE (1 : α) :=
  ⟨Self.zero_le_one⟩

instance instOneNeZero : NeZero (1 : α) :=
  ⟨by
    let ⟨a, b, a_ne_b⟩ := Self.exists_pair_ne
    intro wrong
    apply a_ne_b ; clear a_ne_b
    rw [← mul_one a, ← mul_one b, wrong]
    simp [mul_zero]⟩

instance instOrderedAddCommMonoid : OrderedAddCommMonoid α where
  add_le_add_left := Self.add_le_add_left

instance instCovariantAddLE : CovariantClass α α (· + ·) (· ≤ ·) where
  elim _ _ _ h := StrictOrderedRing.add_le_add_left _ _ h _

instance instCovariantSwapAddLE : CovariantClass α α (swap (· + ·)) (· ≤ ·) where
  elim c a b h := by
    simp [swap, AddCommMagma.add_comm]
    apply add_le_add_left h c

instance instCovariantAddLT : CovariantClass α α (· + ·) (· < ·) where
  elim c a b := by
    simp [lt_iff_le_not_le]
    intro hab nhba
    apply And.intro (add_le_add_left hab c)
    intro h
    let assoc := add_assoc (α := α)
    let hba := add_le_add_left h (- c)
    simp [← assoc (-c) c b, ← assoc (-c) c a, add_left_neg, zero_add] at hba
    contradiction

instance instCovariantSwapAddLT : CovariantClass α α (swap (· + ·)) (· < ·) where
  elim c a b h := by
    simp [swap, AddCommMagma.add_comm]
    apply instCovariantAddLT.elim c h

theorem nsmul_one {n : Nat} : (n : Nat) * 1 = (n : α) := by
  simp [mul_one]
end StrictOrderedRing



class LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α

instance LinearOrderedRing.instOrderedAddCommMonoid
  [Self : LinearOrderedRing α]
: OrderedAddCommMonoid α where
  toAddCommMonoid := Self.toAddCommMonoid
  add_le_add_left := Self.add_le_add_left

namespace Lor
variable [Self : LinearOrderedRing α]

theorem neg_zero : (- 0 : α) = 0 := by
  rw [← Self.add_zero (-0)]
  simp only [Self.add_left_neg]

variable {a b : α}

theorem le_add_left : a ≤ b → (c : α) → c + a ≤ c + b :=
  Self.add_le_add_left a b

theorem le_add_right : a ≤ b → (c : α) → a + c ≤ b + c
| h, c => Self.add_comm c a ▸ Self.add_comm c b ▸ add_le_add_left h c

theorem le_move_right : a ≤ b → 0 ≤ -a + b
| h => Self.add_left_neg a ▸ le_add_left h (-a)

theorem le_move_left : a ≤ b → -b + a ≤ 0
| h => Self.add_left_neg b ▸ le_add_left h (-b)

theorem neg_le : -a ≤ b ↔ -b ≤ a := by
  constructor <;> intro h
  · let h := le_move_left h |> (le_add_right · a)
    simp [add_assoc, add_left_neg, zero_add, add_zero] at h
    assumption
  · let h := le_move_left h |> (le_add_right · b)
    simp [add_assoc, add_left_neg, zero_add, add_zero] at h
    assumption

theorem neg_le_neg_iff : -a ≤ -b ↔ b ≤ a :=
  ⟨ fun h => neg_neg b ▸ neg_le.mp h,
    fun h => by
      rw [neg_le, neg_neg]
      assumption ⟩

theorem le_neg : a ≤ -b ↔ b ≤ -a := by
  constructor
  · intro h
    rw [← neg_neg a, Lor.neg_le_neg_iff] at h
    assumption
  · intro h
    rw [← neg_neg b, Lor.neg_le_neg_iff] at h
    assumption



theorem lt_add_left : a < b → (c : α) → c + a < c + b := by
  simp [-not_lt, -not_le, Self.lt_iff_le_not_le]
  intro hab nhba c
  constructor
  · exact le_add_left hab c
  · intro wrong
    let wrong := le_add_left wrong (-c)
    simp [← add_assoc, add_left_neg, zero_add] at wrong
    contradiction

theorem lt_add_right : a < b → (c : α) → a + c < b + c := by
  intro h c
  rw [add_comm a c, add_comm b c]
  exact lt_add_left h c

theorem lt_move_right : a < b → 0 < -a + b
| h => Self.add_left_neg a ▸ lt_add_left h (-a)

theorem lt_move_left : a < b → -b + a < 0
| h => Self.add_left_neg b ▸ lt_add_left h (-b)

theorem neg_lt : -a < b ↔ -b < a := by
  constructor <;> intro h
  · let h := lt_move_left h |> (lt_add_right · a)
    simp [add_assoc, add_left_neg, zero_add, add_zero] at h
    assumption
  · let h := lt_move_left h |> (lt_add_right · b)
    simp [add_assoc, add_left_neg, zero_add, add_zero] at h
    assumption

theorem neg_lt_neg_iff : -a < -b ↔ b < a :=
  ⟨ fun h => neg_neg b ▸ neg_lt.mp h,
    fun h => by
      rw [neg_lt, neg_neg]
      assumption ⟩

theorem lt_neg : a < -b ↔ b < -a := by
  constructor
  · intro h
    rw [← neg_neg a, Lor.neg_lt_neg_iff] at h
    assumption
  · intro h
    rw [← neg_neg b, Lor.neg_lt_neg_iff] at h
    assumption

def natCast : Nat → α := Self.natCast
end Lor

namespace LinearOrderedRing
variable [Self : LinearOrderedRing α]

instance toInstPreorder [LinearOrderedRing α] : Preorder α :=
  inferInstance
end LinearOrderedRing



class FloorRing (α : Type u) [LinearOrderedRing α] where
  floor : α → Int
  ceil : α → Int
  gc_coe_floor : GaloisConnection Int.cast floor
  gc_ceil_coe : GaloisConnection ceil Int.cast



class Archimedean (α) [OrderedAddCommMonoid α] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : α) {y : α}, 0 < y → ∃ n : Nat, x ≤ n * y



namespace Archimedean
variable [StrictOrderedRing α] [Archimedean α]

theorem lt_of_le_of_lt [Preorder α] : ∀ {a b c : α}, a ≤ b → b < c → a < c
  | _a, _b, _c, hab, hbc =>
    let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc
    lt_of_le_not_le (le_trans hab hbc) fun hca => hcb (le_trans hca hab)
