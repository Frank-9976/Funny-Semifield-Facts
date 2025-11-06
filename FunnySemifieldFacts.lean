/-
Copyright (C) 2025 by Keith J. Bauer.
See file LICENSE for more details.
-/
import Mathlib

/-!
# Funny Semifield Facts
* This repository collects some cute facts about semifields.
* Semifields are semirings whose multiplication is a group with zero.

## Key definitions:
* true semifield: a semifield that is not a field. (I coined this name.)
* AddCSemiMulCGroup: a group that distributes over an additive commutative semigroup.
* ℓ-group: a lattice-ordered abelian group. (This name is commonly used in literature.)

## Summary of what is proven:
* A semifield that has a root to x + 1 = 0 is automatically a field.
* A true semifield without zero is an AddCSemiMulCGroup.
* An AddCSemiMulCGroup with zero is a true semifield.
* An AddCSemiMulCGroup with idempotent addition is an ℓ-group, and vice-versa.
-/

variable (α : Type)

/-- A semifield that has a root to x + 1 = 0 is automatically a field. -/
def Field.ofSemifield [Semifield α] {neg_one : α} (h : neg_one + 1 = 0) : Field α where
  neg a := neg_one * a
  neg_add_cancel a := by
    nth_rw 2 [← one_mul a]
    rw [← right_distrib, h, zero_mul]
  zsmul := by
    have : Neg α := by
      constructor
      intro a
      use neg_one * a
    use zsmulRec
  mul_inv_cancel := Semifield.mul_inv_cancel
  inv_zero := Semifield.inv_zero
  nnqsmul := _
  qsmul := _
  nnratCast_def := Semifield.nnratCast_def

/-- A TrueSemifield is a semifield that is not a field. -/
class TrueSemifield extends Semifield α where
  plus_one_nz (a : α) : a + 1 ≠ 0

/-- An AddCSemiMulCGroup is a group that distributes over an additive commutative semigroup. -/
class AddCSemiMulCGroup extends AddCommSemigroup α, CommGroup α, LeftDistribClass α

/-- Because multiplication is commutative, left_distrib implies right_distrib. -/
instance AddCSemiMulCGroup.toRightDistribClass [AddCSemiMulCGroup α] : RightDistribClass α where
  right_distrib a b c := by
    rw [← mul_comm c, mul_comm a, mul_comm b, left_distrib]

namespace TrueSemifield

/-! ### Facts about true semifields, which are semifields that are not fields. -/

/-- In a true semifield, if b is nonzero, then a + b is nonzero. -/
def add_nz [TrueSemifield α] (a : α) {b : α} (bnz : b ≠ 0) : a + b ≠ 0 := by
  intro h1
  have h2 : (a + b) * b⁻¹ = 0 := by rw [h1, zero_mul]
  rw [right_distrib, mul_inv_cancel₀ bnz] at h2
  exact plus_one_nz (a * b⁻¹) h2

/-- The nonzero elements of a true semifield form an additive subsemigroup. -/
def toAddSubsemigroup [TrueSemifield α] : AddSubsemigroup α where
  carrier := {a : α | a ≠ 0}
  add_mem' := by
    intro a b anz bnz
    exact add_nz α a bnz

instance [TrueSemifield α] : AddCommSemigroup {a : α | a ≠ 0} :=
  AddMemClass.toAddCommSemigroup (toAddSubsemigroup α)

/-- In any semifield, if a and b are nonzero, then a * b is nonzero. -/
def nz_mul_nz [Semifield α] {a b : α} (anz : a ≠ 0) (bnz : b ≠ 0) : a * b ≠ 0 := by
  intro h1
  have h2 : a⁻¹ * (a * b) * b⁻¹ = 0 := by rw[h1, mul_zero, zero_mul]
  rw [← mul_assoc, inv_mul_cancel₀ anz, one_mul, mul_inv_cancel₀ bnz] at h2
  exact one_ne_zero h2

/-- The nonzero elements of any semifield form a multiplicative submonoid. -/
def toSubmonoid [Semifield α] : Submonoid α where
  carrier := {a : α | a ≠ 0}
  mul_mem' := by
    intro a b anz bnz
    exact nz_mul_nz α anz bnz
  one_mem' := one_ne_zero

instance [Semifield α] : CommMonoid {a : α | a ≠ 0} :=
  Submonoid.toCommMonoid (toSubmonoid α)

/-- In any semifield, if a is nonzero, then a⁻¹ is nonzero. -/
def inv_nz [Semifield α] {a : α} (anz : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro h
  apply anz
  symm
  rw [← zero_eq_inv, h]

/-- There is a well-defined inversion on the nonzero elements of any semifield. -/
instance [Semifield α] : Inv {a : α | a ≠ 0} where
  inv a := ⟨a.val⁻¹, inv_nz α a.prop⟩

/-- The nonzero elements of a true semifield form an AddCSemiMulCGroup. -/
instance toAddCSemiMulCGroup [TrueSemifield α] : AddCSemiMulCGroup {a : α | a ≠ 0} where
  inv_mul_cancel := by
    intro a
    have h1 := inv_mul_cancel₀ a.prop
    have h2 : (a.val)⁻¹ = a⁻¹.val := by rfl
    have h3 : a⁻¹.val * a.val = (a⁻¹ * a).val := by rfl
    rw [h2, h3] at h1
    ext
    rw [h1]
    rfl
  left_distrib := by
    intro a b c
    have h1 := left_distrib a.val b.val c.val
    have h2 (a b : {a : α | a ≠ 0}) : a.val + b.val = (a + b).val := by rfl
    have h3 (a b : {a : α | a ≠ 0}) : a.val * b.val = (a * b).val := by rfl
    repeat rw [h2, h3] at h1
    ext
    rw [h1]
    rfl

/-- Adding a 0 to an AddCSemiMulCGroup results in a true semifield. -/
instance [AddCSemiMulCGroup α] : AddCommMonoid (WithZero α) := WithZero.instAddCommMonoid

instance [AddCSemiMulCGroup α] : CommGroupWithZero (WithZero α) := WithZero.instCommGroupWithZero

instance ofAddCSemiMulCGroup [AddCSemiMulCGroup α] : TrueSemifield (WithZero α) where
  left_distrib a b c := by
    cases a
    · rw [zero_mul, zero_mul, zero_mul, zero_add]
    · cases b
      · rw [mul_zero, zero_add, zero_add]
      · cases c
        · rw [mul_zero, add_zero, add_zero]
        · rw [left_distrib]
  right_distrib a b c := by
    cases c
    · rw [mul_zero, mul_zero, mul_zero, zero_add]
    · cases a
      · rw [zero_mul, zero_add, zero_add]
      · cases b
        · rw [zero_mul, add_zero, add_zero]
        · rw [right_distrib]
  nnqsmul := _
  plus_one_nz a := by
    cases a
    · rw [zero_add]
      exact one_ne_zero
    · exact WithZero.coe_ne_zero

end TrueSemifield

/-- A LatticeOrderedCommGroup is a lattice-ordered abelian group, often known as an `ℓ-group`. -/
class LatticeOrderedCommGroup extends Lattice α, CommGroup α, IsOrderedMonoid α

/-- An IdemAddCSemiMulCGroup is an AddCSemiMulCGroup where 2 = 1. -/
class IdemAddCSemiMulCGroup extends AddCSemiMulCGroup α where
  two_eq_one : 1 + 1 = (1 : α)

namespace IdemAddCSemiMulCGroup

/-! ### Facts about the class IdemAddCSemiMulCGroup. -/

instance [IdemAddCSemiMulCGroup α] : LE α where
  le a b := a + b = b

def le_simp [IdemAddCSemiMulCGroup α] (a b : α) : a ≤ b ↔ a + b = b := by rfl

/-- In an AddCSemiMulCGroup, 2 = 1 implies idempotent addition. -/
def idempotent [IdemAddCSemiMulCGroup α] (a : α) : a + a = a := by
  nth_rw 1 2 [← mul_one a]
  rw [← left_distrib a 1 1, two_eq_one, mul_one]

/-- Any IdemAddCSemiMulCGroup forms an ℓ-group. -/
instance [IdemAddCSemiMulCGroup α] : SemilatticeSup α where
  le_refl a := by
    rw [le_simp, idempotent]
  le_trans a b c h1 h2 := by
    rw [← h2, le_simp, ← add_assoc, h1]
  le_antisymm a b h1 h2 := by
    rw [← h1]
    nth_rw 1 [← h2]
    rw [add_comm]
  sup a b := a + b
  le_sup_left a b := by
    rw [le_simp, ← add_assoc, idempotent]
  le_sup_right a b := by
    rw [add_comm a b, le_simp, ← add_assoc, idempotent]
  sup_le a b c h1 h2 := by
    rw [le_simp, add_assoc, h2, h1]

instance [IdemAddCSemiMulCGroup α] : IsOrderedMonoid α where
  mul_le_mul_left a b h c := by
    have goal : c * a + c * b = c * b := by
      rw [← left_distrib, h]
    exact goal

instance toLatticeOrderedCommGroup [IdemAddCSemiMulCGroup α] : LatticeOrderedCommGroup α where
  inf a b := (a⁻¹ ⊔ b⁻¹)⁻¹
  inf_le_left a b := by
    rw [inv_le']
    exact le_sup_left
  inf_le_right a b := by
    rw [inv_le']
    exact le_sup_right
  le_inf a b c h1 h2 := by
    rw [← inv_inv a, inv_le', inv_inv]
    rw [← inv_inv a, inv_le'] at h1
    rw [← inv_inv a, inv_le'] at h2
    exact sup_le h1 h2

/-- Any ℓ-group forms an IdemAddCSemiMulCGroup. -/
instance ofLatticeOrderedCommGroup [LatticeOrderedCommGroup α] : IdemAddCSemiMulCGroup α where
  add a b := a ⊔ b
  add_assoc := sup_assoc
  add_comm := sup_comm
  left_distrib a b c := by
    have h1 := IsOrderedMonoid.mul_le_mul_left b (b ⊔ c) le_sup_left a
    have h2 := IsOrderedMonoid.mul_le_mul_left c (b ⊔ c) le_sup_right a
    have h3 := sup_le h1 h2
    have h4 := IsOrderedMonoid.mul_le_mul_left (a * b) (a * b ⊔ a * c) le_sup_left a⁻¹
    have h5 := IsOrderedMonoid.mul_le_mul_left (a * c) (a * b ⊔ a * c) le_sup_right a⁻¹
    have h6 := sup_le h4 h5
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, one_mul] at h6
    have h7 := IsOrderedMonoid.mul_le_mul_left (b ⊔ c) (a⁻¹ * (a * b ⊔ a * c)) h6 a
    rw [← mul_assoc, mul_inv_cancel, one_mul] at h7
    exact le_antisymm h7 h3
  two_eq_one := sup_idem 1

end IdemAddCSemiMulCGroup
