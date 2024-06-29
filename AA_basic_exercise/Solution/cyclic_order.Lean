import Mathlib

open Set
open Subgroup MonoidHom

--Cyclic group is communitive
example {G : Type*} [Group G] (h : IsCyclic G) (a b : G) : a * b = b * a := by
  rcases h with ⟨g,hg⟩
  have Ha : ∃ m : ℤ , g ^ m = a := by apply Subgroup.mem_zpowers_iff.mp (hg a)
  have Hb : ∃ n : ℤ , g ^ n = b := by apply Subgroup.mem_zpowers_iff.mp (hg b)
  rcases Ha with ⟨m,ha⟩
  rcases Hb with ⟨n,hb⟩
  rw [← ha, ← hb]
  have mul₁ : g ^ m * g ^ n = g ^ (m + n) := by exact (zpow_add g m n).symm
  have mul₂ : g ^ n * g ^ m = g ^ (n + m) := by exact (zpow_add g n m).symm
  simp [mul₁,mul₂]
  congr 1
  exact add_comm m n

--Cyclic group is communitive , another possible solution
example {G : Type*} [Group G] (h : IsCyclic G) (a b : G) : a * b = b * a := by
  rcases h with ⟨g,hg⟩
  have Ha : ∃ m : ℤ , g ^ m = a := by apply Subgroup.mem_zpowers_iff.mp (hg a)
  have Hb : ∃ n : ℤ , g ^ n = b := by apply Subgroup.mem_zpowers_iff.mp (hg b)
  rcases Ha with ⟨m,ha⟩
  rcases Hb with ⟨n,hb⟩
  rw [← ha, ← hb]
  calc
    _= g ^ (m + n) := by exact Eq.symm (zpow_add g m n)
    _= g ^ (n + m) := by
      have : m + n = n + m := by ring
      rw [this]
    _=_ := by exact zpow_add g n m


--dierct product
example {G H : Type*} [Group G] [Group H] (h : IsCyclic (G × H) ) : IsCyclic G := by
  rcases h with ⟨a,ha⟩
  use a.1
  intro x
  rcases (ha (x,1)) with ⟨n,hn⟩
  use n
  calc
    _=(a ^ n).1 := rfl
    _=_ := by simp only [hn]

example {G H : Type*} [Group G] [Group H] (a : G × H ) : orderOf a = Nat.lcm (orderOf a.1) (orderOf a.2) := by
  have dvd1 :  orderOf a.1 ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _=(a ^ orderOf a).1 := rfl
      _=_ := by simp only [pow_orderOf_eq_one a, Prod.fst_one]
  have dvd2 :  orderOf a.2 ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _=(a ^ orderOf a).2 := rfl
      _=_ := by simp only [pow_orderOf_eq_one a, Prod.snd_one]
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
    _= (a.1 ^ Nat.lcm (orderOf a.1) (orderOf a.2), a.2 ^ Nat.lcm (orderOf a.1) (orderOf a.2)) := rfl
    _=_ := by simp only [eq1, eq2, Prod.mk_eq_one, and_self]
  apply Nat.dvd_antisymm h2 h1
