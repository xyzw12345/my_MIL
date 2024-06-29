import Mathlib

open Set
open Subgroup

--induction
theorem eqord {G : Type*} [Group G] (a b : G) : orderOf (a * b) = orderOf (b * a) := by
  have : ∀ k : ℕ , b * (a * b) ^ k = (b * a) ^ k * b := by
    intro k
    induction' k with k ih
    · simp only [pow_zero, mul_one, one_mul]
    · calc
        _=b * (a * b) ^ k * (a * b) := by rw [pow_succ (a * b) k];group
        _=(b * a) ^ k * (b * a) * b := by rw[ih];group
        _=_:= by rw [pow_succ (b * a) k];group
  have div1 : orderOf (a * b) ∣ orderOf (b * a) := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _= b⁻¹ * (b * (a * b) ^ orderOf (b * a)) := by group
      _= b⁻¹ * (b * a) ^ orderOf (b * a) * b := by rw [this (orderOf (b * a))];group
      _= b⁻¹ * 1 * b := by rw[pow_orderOf_eq_one (b * a)]
      _=_ := by group
  have div2 : orderOf (b * a) ∣ orderOf (a * b) := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _= (b * a) ^ orderOf (a * b) * b * b⁻¹ := by group
      _= b * (a * b) ^ orderOf (a * b) * b⁻¹ := by rw [this (orderOf (a * b))];group
      _= b * 1 * b⁻¹ := by rw[pow_orderOf_eq_one (a * b)]
      _=_ := by group
  apply Nat.dvd_antisymm div1 div2

theorem eqord3 {G : Type*} [Group G] (a b c : G) : orderOf (a * b * c) = orderOf (c * a * b) := by
  calc
    _= orderOf (c * (a * b)) := eqord (a * b) c
    _=_ := by congr 1;group
