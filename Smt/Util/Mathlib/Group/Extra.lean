/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Smt.Util.Mathlib.Algebra
import Smt.Util.Mathlib.Covariant
import Smt.Util.Mathlib.Group.Nat
import Smt.Util.Mathlib.Group.Int


namespace Smt



namespace Int

variable [LinearOrderedRing α] [FloorRing α]

/-- `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`. -/
def floor : α → Int :=
  FloorRing.floor

/-- `Int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`. -/
def ceil : α → Int :=
  FloorRing.ceil

/-- `Int.fract a`, the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α :=
  a - floor a

@[simp]
theorem floor_int : (Int.floor : Int → Int) = id :=
  rfl

@[simp]
theorem ceil_int : (Int.ceil : Int → Int) = id :=
  rfl

@[simp]
theorem fract_int : (Int.fract : Int → Int) = fun _ => 0 :=
  funext fun x => by simp [fract]

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a
end Int



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
end Archimedean



namespace Int
instance instLinearOrderedRing : LinearOrderedRing Int where
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

abbrev toLor := @instLinearOrderedRing

theorem neg_zero : -(0 : Int) = 0 := rfl



section
variable [I : AddGroupWithOne R]

theorem cast_zero : ((0 : Int) : R) = 0 :=
  (AddGroupWithOne.intCast_ofNat 0).trans Nat.cast_zero

theorem cast_neg : ∀ n, ((-n : Int) : R) = -n
  | (0 : Nat) => by
    erw [cast_zero, ← I.add_zero (-0), I.add_left_neg]
  | (n + 1 : Nat) => by
    simp only [I.intCast_ofNat (n + 1), ← I.intCast_negSucc]
    rfl
  | .negSucc n => by
    simp only [Int.neg_negSucc, I.intCast_negSucc, neg_neg]
    erw [← I.intCast_ofNat]
end

protected
theorem le.dest_sub {a b : Int} (h : a ≤ b) : ∃ n : Nat, b - a = n := by
  apply Int.nonneg_def.1
  let h := Lor.le_move_right h
  rw [add_comm] at h
  assumption

protected
theorem le.dest {a b : Int} (h : a ≤ b) : ∃ n : Nat, a + n = b :=
  let ⟨n, h₁⟩ := le.dest_sub h
  ⟨ n,
    by
      rw [← h₁, Int.add_comm]
      simp [add_assoc, add_left_neg] ⟩

end Int



namespace Nat
variable {p : Nat → Prop} [DecidablePred p] (H : ∃ n, p n)

private
def lbp (m n : Nat) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

private
def wf_lbp : WellFounded (@lbp p) := ⟨
  let ⟨n, pn⟩ := H
  suffices ∀ m k, n ≤ k + m → Acc lbp k from fun a => this _ _ (Nat.le_add_left _ _)
  fun m =>
    Nat.recOn m
      (fun k kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩
⟩

protected noncomputable
def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _
    (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m })
    lbp
    (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0
    fun n h => absurd h (Nat.not_lt_zero _)

protected noncomputable
def find : Nat :=
  (Nat.findX H).1

protected
theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left

protected
theorem find_min : ∀ {m : Nat}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right

protected
theorem find_min' {m : Nat} (h : p m) : Nat.find H ≤ m :=
  Nat.le_of_not_lt fun l => Nat.find_min H l h

end Nat



namespace Int
noncomputable
def leastOfBdd
  {P : Int → Prop} [DecidablePred P]
  (b : Int) (Hb : ∀ z : Int, P z → b ≤ z) (Hinh : ∃ z : Int, P z)
: { lb : Int // P lb ∧ ∀ z : Int, P z → lb ≤ z } :=
  have EX : ∃ n : Nat, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : Int), Nat.find_spec EX, fun z h =>
    match z, le.dest (Hb _ h), h with
    | _, ⟨_, rfl⟩, h => add_le_add_left (Int.ofNat_le.2 <| Nat.find_min' _ h) _⟩

noncomputable
def greatestOfBdd
  {P : Int → Prop} [DecidablePred P] (b : Int) (Hb : ∀ z : Int, P z → z ≤ b)
  (Hinh : ∃ z : Int, P z) : { ub : Int // P ub ∧ ∀ z : Int, P z → z ≤ ub }
:=
  have Hbdd' : ∀ z : Int, P (-z) → -b ≤ z := fun z h => Lor.neg_le.1 (Hb _ h)
  have Hinh' : ∃ z : Int, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
  ⟨-lb, Plb, fun z h => Lor.le_neg.1 <| al _ <| by rwa [neg_neg]⟩

theorem exists_greatest_of_bdd
  {P : Int → Prop}
  (Hbdd : ∃ b : Int , ∀ z : Int , P z → z ≤ b)
  (Hinh : ∃ z : Int , P z)
: ∃ ub : Int , P ub ∧ ∀ z : Int , P z → z ≤ ub := by
  haveI := Classical.propDecidable
  let ⟨b, Hb⟩ := Hbdd
  let ⟨lb, H⟩ := greatestOfBdd b Hb Hinh
  exact ⟨lb, H⟩
end Int



section top
variable [Self : AddGroupWithOne α]

@[simp] theorem ofNat_eq_coe : Int.ofNat n = Nat.cast n := rfl

@[simp, norm_cast]
theorem Nat.cast_sub {m n} (h : m ≤ n) : ((n - m : Nat) : α) = n - m :=
  eq_sub_of_add_eq <| by rw [← cast_add, Nat.sub_add_cancel h]

@[simp high, norm_cast]
theorem Int.cast_ofNat (n : Nat) : ((n : Int) : α) = n :=
  AddGroupWithOne.intCast_ofNat _

theorem cast_negSucc (n : Nat) : (Int.negSucc n : α) = -(n + 1 : Nat) :=
  AddGroupWithOne.intCast_negSucc n

@[simp, norm_cast]
theorem Int.cast_subNatNat (m n : Nat) : ((Int.subNatNat m n : α) : α) = m - n := by
  unfold Int.subNatNat
  cases e : n - m
  · simp only [ofNat_eq_coe, cast_ofNat]
    simp only [Nat.le_of_sub_eq_zero e, Nat.cast_sub]
  · rw [
    cast_negSucc, Nat.add_one, ← e,
    Nat.cast_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ e,
    neg_sub (α := α)
  ]

@[simp]
theorem Int.cast_add : ∀ m n, ((m + n : Int) : α) = m + n
| (m : Nat), (n : Nat) => by
  simp only [← Int.ofNat_add, cast_ofNat, cast_add]
  simp only [Nat.cast_add]
| (m : Nat), .negSucc n => by erw [cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_add_neg]
| .negSucc m, (n : Nat) => by
  erw [
    cast_subNatNat, cast_ofNat, cast_negSucc, sub_eq_iff_eq_add, add_assoc,
    eq_neg_add_iff_add_eq, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm
  ]
| .negSucc m, .negSucc n =>
  show (Int.negSucc (m + n + 1) : α) = _ by
    rw [cast_negSucc, cast_negSucc, cast_negSucc, ← neg_add_rev, ← Nat.cast_add,
      Nat.add_right_comm m n 1, Nat.add_assoc, Nat.add_comm]

theorem cast_sub (m n) : ((m - n : Int) : α) = m - n := by
  simp [Int.sub_eq_add_neg, sub_eq_add_neg, Int.cast_neg, Int.cast_add]
end top



section top
variable [StrictOrderedRing α]

@[simp low]
theorem Nat.cast_nonneg' (n : Nat) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

@[simp]
theorem Nat.cast_nonneg (n : Nat) : 0 ≤ (n : α) :=
  cast_nonneg' n

@[simp]
theorem Int.cast_nonneg [StrictOrderedRing α] : ∀ {n : Int}, (0 : α) ≤ n ↔ 0 ≤ n
  | (n : Nat) => by simp only [cast_ofNat, cast_nonneg, Nat.cast_nonneg]
  | Int.negSucc n => by
    have : -(n : α) < 1 :=
      lt_of_le_of_lt
        (by simp only [Left.neg_nonpos_iff, Nat.cast_nonneg])
        zero_lt_one
    simpa only [
      cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      ← sub_eq_add_neg, sub_nonneg, le_neg, LT.not_le (Int.negSucc_lt_zero n), iff_false
    ] using LT.not_le this

theorem Int.cast_le {m n : Int} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]
end top


section
variable {M : Type u} [Self : OrderedAddCommMonoid α]

theorem pow_zero (a : α) : 0 * a = 0 :=
  Self.zero_mul a

theorem add_nsmul (a : α) (m n : Nat) : (m + n) * a = m * a + n * a := by
  induction n with
  | zero => rw [Nat.add_zero, Self.zero_mul, Self.add_zero]
  | succ _ ih => rw [Self.succ_mul, ← add_assoc, ← ih, ← Self.succ_mul, Nat.add_assoc]

theorem nsmul_lt_nsmul_left
  [CovariantClass α α (· + ·) (· < ·)]
  {a : α} {n m : Nat} (ha : 0 < a) (h : n < m)
: n * a < m * a := by
  rcases Nat.le.dest h with ⟨k, rfl⟩; clear h
  rw [add_nsmul, Self.succ_mul, Self.add_assoc, ← Self.succ_mul']
  apply lt_add_of_pos_right _ (Self.mul_pos a ha)

theorem exists_lt_nsmul
  [Archimedean α] [CovariantClass α α (· + ·) (· < ·)]
  {a : α} (ha : 0 < a) (b : α)
: ∃ n : Nat, b < n * a :=
  let ⟨k, hk⟩ := Archimedean.arch b ha
  ⟨k + 1, lt_of_le_of_lt hk <| nsmul_lt_nsmul_left ha k.lt_succ_self⟩
end

section
variable {α : Type u} [Self : StrictOrderedRing α] [Archimedean α]

theorem exists_nat_gt (x : α) : ∃ n : Nat, x < (n : α) := by
  let ⟨n, h_n⟩ := exists_lt_nsmul zero_lt_one x
  exists n
  simp [nsmul_one] at h_n
  assumption

theorem exists_int_gt (x : α) : ∃ n : Int, x < n := by
  let ⟨n, h⟩ := exists_nat_gt x
  exists n
  simp only [Self.intCast_ofNat]
  assumption

theorem exists_int_lt (x : α) : ∃ n : Int, (n : α) < x := by
  let ⟨n, h⟩ := exists_int_gt (-x)
  exists -n
  rw [Int.cast_neg, neg_lt]
  assumption

theorem exists_floor (x : α)
: ∃ fl : Int, ∀ z : Int, z ≤ fl ↔ (z : α) ≤ x := by
  haveI := Classical.propDecidable
  have : ∃ ub : Int, (ub : α) ≤ x ∧ ∀ z : Int, (z : α) ≤ x → z ≤ ub :=
    Int.exists_greatest_of_bdd
      (let ⟨n, hn⟩ := exists_int_gt x
      ⟨n, fun z h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
      (let ⟨n, hn⟩ := exists_int_lt x
      ⟨n, le_of_lt hn⟩)
  refine' this.imp fun fl h z => _
  cases h with
  | intro h₁ h₂ =>
    exact ⟨fun h => le_trans (Int.cast_le.2 h) h₁, h₂ z⟩
end


namespace FloorRing

def ofFloor
  (α : Type u) [LinearOrderedRing α] (floor : α → Int)
  (gc_coe_floor : GaloisConnection Int.cast floor) : FloorRing α
where
  floor := floor
  ceil := fun a => -floor (-a)
  gc_coe_floor := gc_coe_floor
  gc_ceil_coe := fun a z => by
    simp
    rw [neg_le, ← gc_coe_floor, Int.cast_neg, Lor.neg_le_neg_iff]

end FloorRing


section scope
variable (α : Type u) [LinearOrderedRing α] [Archimedean α]

namespace Archimedean
noncomputable
def Archimedean.floorRing : FloorRing α :=
  FloorRing.ofFloor α (fun a => Classical.choose (exists_floor a)) fun z a =>
    (Classical.choose_spec (exists_floor a) z).symm
end Archimedean
