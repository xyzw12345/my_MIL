import Mathlib

section Cyclic_Groups

example {G : Type*} [Group G] (h : IsCyclic G) (a b : G) : a * b = b * a := by
  rcases h with ⟨g, hg⟩
  have Ha : ∃ m : ℤ , g ^ m = a := by apply Subgroup.mem_zpowers_iff.mp (hg a)
  have Hb : ∃ n : ℤ , g ^ n = b := by apply Subgroup.mem_zpowers_iff.mp (hg b)
  rcases Ha with ⟨m, ha⟩
  rcases Hb with ⟨n, hb⟩
  rw [← ha, ← hb]
  calc
    _= g ^ (m + n) := by exact Eq.symm (zpow_add g m n)
    _= g ^ (n + m) := by
      have : m + n = n + m := by ring
      rw [this]
    _=_ := by exact zpow_add g n m

end Cyclic_Groups

section Order

#check orderOf_dvd_iff_pow_eq_one
#check orderOf_eq_zero_iff'

example {G H : Type*} [Group G] [Group H] (a : G × H ) : orderOf a = Nat.lcm (orderOf a.1) (orderOf a.2) := by
  have dvd1 :  orderOf a.1 ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = (a ^ orderOf a).1 := rfl
      _ = _ := by simp only [pow_orderOf_eq_one a, Prod.fst_one]
  have dvd2 :  orderOf a.2 ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = (a ^ orderOf a).2 := rfl
      _ = _ := by simp only [pow_orderOf_eq_one a, Prod.snd_one]
  have h1 : Nat.lcm (orderOf a.1) (orderOf a.2) ∣ orderOf a :=  Nat.lcm_dvd dvd1 dvd2
  have h2 : orderOf a ∣ Nat.lcm (orderOf a.1) (orderOf a.2) := by
    apply orderOf_dvd_of_pow_eq_one
    have eq1 : a.1 ^ Nat.lcm (orderOf a.1) (orderOf a.2) = 1:= by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_lcm_left (orderOf a.1) (orderOf a.2)
    have eq2 : a.2 ^ Nat.lcm (orderOf a.1) (orderOf a.2) = 1:= by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact Nat.dvd_lcm_right (orderOf a.1) (orderOf a.2)
    calc
    _ = (a.1 ^ Nat.lcm (orderOf a.1) (orderOf a.2), a.2 ^ Nat.lcm (orderOf a.1) (orderOf a.2)) := rfl
    _ = _ := by simp only [eq1, eq2, Prod.mk_eq_one, and_self]
  apply Nat.dvd_antisymm h2 h1

theorem eqord {G : Type*} [Group G] (a b : G) : orderOf (a * b) = orderOf (b * a) := by
  have : ∀ k : ℕ , b * (a * b) ^ k = (b * a) ^ k * b := by
    intro k
    induction' k with k ih
    · simp only [pow_zero, mul_one, one_mul]
    · calc
        _ = b * (a * b) ^ k * (a * b) := by rw [pow_succ (a * b) k]; group
        _ = (b * a) ^ k * (b * a) * b := by rw[ih]; group
        _ = _:= by rw [pow_succ (b * a) k]; group
  have div1 : orderOf (a * b) ∣ orderOf (b * a) := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = b⁻¹ * (b * (a * b) ^ orderOf (b * a)) := by group
      _ = b⁻¹ * (b * a) ^ orderOf (b * a) * b := by rw [this (orderOf (b * a))]; group
      _ = b⁻¹ * 1 * b := by rw [pow_orderOf_eq_one (b * a)]
      _ = _ := by group
  have div2 : orderOf (b * a) ∣ orderOf (a * b) := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = (b * a) ^ orderOf (a * b) * b * b⁻¹ := by group
      _ = b * (a * b) ^ orderOf (a * b) * b⁻¹ := by rw [this (orderOf (a * b))];
      _ = b * 1 * b⁻¹ := by rw [pow_orderOf_eq_one (a * b)]
      _ = _ := by group
  apply Nat.dvd_antisymm div1 div2

end Order
