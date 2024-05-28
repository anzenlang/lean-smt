/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Smt.Util.Mathlib.Algebra
import Smt.Util.Mathlib.Covariant


namespace Smt



class Zero (α : Type u) where
  zero : α

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α 0 where
  ofNat := ‹Zero α›.1

instance (priority := 200) Zero.ofOfNat0 {α} [OfNat α 0] : Zero α where
  zero := 0

class One (α : Type u) where
  one : α

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α 1 where
  ofNat := ‹One α›.1
instance (priority := 200) One.ofOfNat1 {α} [OfNat α 1] : One α where
  one := 1

protected def Nat.unaryCast [One α] [Zero α] [Add α] : Nat → α
| 0 => 0
| n + 1 => Nat.unaryCast n + 1

def Nat.npowRec [One α] [Mul α] : Nat → α → α
| 0, _ => 1
| n + 1, a => npowRec n a * a

protected def Int.castDef {α : Type u} [NatCast α] [Neg α] : Int → α
| (n : Nat) => n
| Int.negSucc n => -(n + 1 : Nat)



class AddZeroClass (α : Type u) extends Zero α, Add α where
  protected zero_add : ∀ a : α, 0 + a = a
  protected add_zero : ∀ a : α, a + 0 = a

instance (priority := 50) [AddZeroClass α] : Add α :=
  AddZeroClass.toAdd

theorem add_zero [AddZeroClass α] : ∀ a : α, a + 0 = a :=
  AddZeroClass.add_zero

theorem zero_add [AddZeroClass α] : ∀ a : α, 0 + a = a :=
  AddZeroClass.zero_add



class MulZeroClass (α : Type u) extends Zero α, Mul α where
  protected zero_mul : ∀ a : α, 0 * a = 0
  protected mul_zero : ∀ a : α, a * 0 = 0

theorem mul_zero [MulZeroClass α] : ∀ a : α, a * 0 = 0 :=
  MulZeroClass.mul_zero

theorem zero_mul [MulZeroClass α] : ∀ a : α, 0 * a = 0 :=
  MulZeroClass.zero_mul



class MulOneClass (α : Type u) extends One α, Mul α where
  protected one_mul : ∀ a : α, 1 * a = a
  protected mul_one : ∀ a : α, a * 1 = a

instance (priority := 50) [MulOneClass α] : Mul α :=
  MulOneClass.toMul

theorem mul_one [MulOneClass α] : ∀ a : α, a * 1 = a :=
  MulOneClass.mul_one

theorem one_mul [MulOneClass α] : ∀ a : α, 1 * a = a :=
  MulOneClass.one_mul



class MulZeroOneClass (α : Type u) extends MulZeroClass α, MulOneClass α



class Distrib (α : Type u) extends Add α, Mul α where
  protected left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c



class AddCommMagma (α : Type u) extends Add α where
  protected add_comm : ∀ a b : α, a + b = b + a



class Semigroup (α : Type u) extends Mul α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)

section top_level
variable [Semigroup α]

theorem mul_assoc : ∀ a b c : α, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc
end top_level



class SemigroupWithZero (α : Type u) extends Semigroup α, MulZeroClass α



class AddSemigroup (α : Type u) extends Add α where
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

section top_level
variable [AddSemigroup α]

theorem add_assoc : ∀ a b c : α, a + b + c = a + (b + c) :=
  AddSemigroup.add_assoc

instance (priority := 50) : Add α :=
  AddSemigroup.toAdd
end top_level



class AddCommSemigroup (α : Type u) extends AddSemigroup α, AddCommMagma α



class AddMonoid (α : Type u) extends AddSemigroup α, AddZeroClass α where
  protected nsmul : Nat → α → α
  protected nsmul_zero : ∀ a : α, nsmul 0 a = 0 :=
    by intros ; simp
  protected nsmul_succ : ∀ (n : Nat) (a : α), nsmul n.succ a = nsmul n a + a :=
    by intros ; simp



class AddMonoidWithOne (α : Type u) extends NatCast α, AddMonoid α, One α where
  natCast := Nat.unaryCast
  natCast_zero : natCast 0 = 0 := by intros ; simp
  natCast_succ : ∀ n : Nat, natCast n.succ = natCast n + 1 := by intros ; simp



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
  protected sub_eq_add_neg : ∀ a b : α, a - b = a + -b := by intros ; simp
  protected zsmul : Int → α → α
  protected zsmul_zero' : ∀ a : α, zsmul 0 a = 0 := by intros ; simp
  protected zsmul_succ' (n : Nat) (a : α) :
    zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a
  := by intros ; simp
  protected zsmul_neg' (n : Nat) (a : α) :
    zsmul (Int.negSucc n) a = -zsmul n.succ a
  := by intros ; simp



class AddGroup (α : Type u) extends SubNegMonoid α where
  protected add_left_neg : ∀ a : α, -a + a = 0

section top_level
variable [AddGroup α]

theorem add_left_neg : ∀ a : α, -a + a = 0 :=
  AddGroup.add_left_neg
end top_level

class AddCommGroup (α : Type u) extends AddGroup α, AddCommMonoid α

section top_level
variable [inst : AddCommGroup α]

theorem add_right_neg : ∀ a : α, a + - a = 0 :=
  fun a => inst.add_comm _ _ ▸ inst.add_left_neg a
end top_level

class AddGroupWithOne (α : Type u) extends IntCast α, AddMonoidWithOne α, AddGroup α where
  /-- The canonical homomorphism `Int → α`. -/
  intCast := Int.castDef
  /-- The canonical homomorphism `Int → α` agrees with the one from `Nat → α` on `Nat`. -/
  intCast_ofNat : ∀ n : Nat, intCast (n : Nat) = Nat.cast n := by intros ; simp
  /-- The canonical homomorphism `Int → α` for negative values is just the negation of the values
  of the canonical homomorphism `Nat → α`. -/
  intCast_negSucc : ∀ n : Nat, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros ; simp

class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  /-- Addition is monotone in an ordered additive commutative group. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b



class InvolutiveNeg (α : Type u) extends Neg α where
  protected neg_neg : ∀ x : α, - -x = x

section top_level

instance [inst : AddCommGroup α] : InvolutiveNeg α where
  neg_neg a := by
    rw [
      ← inst.add_zero (- -a),
      ← inst.add_left_neg a,
      ← inst.add_assoc,
      inst.add_left_neg (- a),
      inst.zero_add
    ]

variable [InvolutiveNeg α]

theorem neg_neg : ∀ x : α, - -x = x :=
  InvolutiveNeg.neg_neg
end top_level



class SubtractionMonoid (α : Type u) extends SubNegMonoid α, InvolutiveNeg α where
  protected neg_add_rev (a b : α) : -(a + b) = -b + -a
  protected neg_eq_of_add (a b : α) : a + b = 0 → -a = b

section top_level
variable [SubtractionMonoid α]
  {a b : α}

theorem neg_eq_of_add_eq_zero_right : a + b = 0 → -a = b :=
  SubtractionMonoid.neg_eq_of_add a b

theorem neg_eq_of_add_eq_zero_left (h : a + b = 0) : -b = a :=
  by rw [← neg_eq_of_add_eq_zero_right h, neg_neg]

theorem eq_neg_of_add_eq_zero_left
  {α : Type u} [SubtractionMonoid α] (h : a + b = 0)
: a = -b := by
  rw [← neg_eq_of_add_eq_zero_left h]
end top_level



class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α



class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α



class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α



class HasDistribNeg (α : Type u) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section top_level

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _
end top_level



class Ring (α : Type u) extends Semiring α, AddCommGroup α, AddGroupWithOne α



class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

section top_level
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
end top_level



class Nontrivial (α : Type u) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y



class StrictOrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α, Nontrivial α where
  /-- In a strict ordered ring, `0 ≤ 1`. -/
  protected zero_le_one : 0 ≤ (1 : α)
  /-- The product of two positive elements is positive. -/
  protected mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

namespace StrictOrderedRing
variable {α : Type u} [StrictOrderedRing α]

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
end StrictOrderedRing



class LinearOrderedRing (α : Type u) extends StrictOrderedRing α, LinearOrder α

namespace LinearOrderedRing
variable [LinearOrderedRing α]

instance instInt : LinearOrderedRing Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_comm := Int.add_comm
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  neg := Int.neg
  decidableLT := inferInstance
  decidableLE := inferInstance
  add_left_neg := Int.add_left_neg
  add_le_add_left := @Int.add_le_add_left
  nsmul := (· * ·)
  nsmul_zero := by simp
  nsmul_succ n a := by simp [Int.ofNat_succ, Int.add_mul]
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  zsmul := (· * ·)
  exists_pair_ne := ⟨0, 1, by simp⟩
  zero_le_one := by simp
  mul_pos := @Int.mul_pos
  le_total := Int.le_total
  natCast_zero := by simp
  natCast_succ := by
    simp [NatCast.natCast, Int.ofNat_succ, Int.add_mul]
  npow_zero := by
    simp [Nat.npowRec]
  npow_succ := by simp [Nat.npowRec]
  sub_eq_add_neg := by
    simp [Int.sub_eq_add_neg, Neg.neg]
  zsmul_zero' := by
    simp
  zsmul_succ' := by simp [Int.ofNat_succ, Int.add_mul]
  zsmul_neg' n a := by
    conv =>
      rhs
      congr
      simp
    rw [← Int.neg_mul]
    simp [Int.neg_ofNat_succ]
  intCast_ofNat := by
    simp [IntCast.intCast]
  intCast_negSucc n := by
    conv =>
      lhs
      simp [IntCast.intCast]
end LinearOrderedRing
