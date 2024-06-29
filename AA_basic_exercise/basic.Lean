import Mathlib

open Set
open Subgroup

--def of Groups
def RootsOfUnity : Set ℂ := {x | ∃ n : ℕ , n > 0 ∧ x^n = 1}

noncomputable instance : Group (RootsOfUnity) where
  mul := by
    intro ⟨x,hx⟩ ⟨y,hy⟩
    use x*y
    rcases hx with ⟨n,np,hx⟩
    rcases hy with ⟨m,mp,hy⟩
    use m*n
    have pos : m * n > 0 := by positivity
    have eq1 : (x * y) ^ (m * n) = 1 := by
      calc
        _= (x ^ n) ^ m * (y ^ m) ^ n := by ring
        _= 1 ^ m * 1 ^ n := by simp [hx,hy]
        _=_ := by simp only [one_pow, mul_one]
    simp only [gt_iff_lt, pos, eq1, and_self]
  mul_assoc := by
    intro ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩
    apply Subtype.val_inj.mp
    show a * b * c = a * (b * c)
    ring
  one := by
    use 1,1
    simp only [gt_iff_lt, zero_lt_one, pow_one, and_self]
  one_mul := by
    intro ⟨a,ha⟩
    apply Subtype.val_inj.mp
    show 1 * a = a
    simp only [one_mul]
  mul_one := by
    intro ⟨a,ha⟩
    apply Subtype.val_inj.mp
    show a * 1 = a
    simp only [mul_one]
  inv := by
    intro ⟨a,ha⟩
    use 1/a
    rcases ha with ⟨n,np,ha⟩
    use n
    have eq1 : (1 / a) ^ n = 1 := by
      calc
        _= 1/(a ^ n) := by ring
        _= 1 := by simp only [ha, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    simp only [gt_iff_lt, np, eq1,and_true]
  mul_left_inv := by
    intro ⟨a,ha⟩
    apply Subtype.val_inj.mp
    show 1/a * a = 1
    apply one_div_mul_cancel
    by_contra h
    rcases ha with ⟨n,np,ha⟩
    rw [h] at ha
    have : (0 : ℂ)  ^ n = (0 : ℂ) := by exact Mathlib.Tactic.Ring.zero_pow np
    rw [ha] at this
    absurd this
    simp only [one_ne_zero, not_false_eq_true]


--basic

example {G : Type*} [Group G] (g : G) (h : ∃ f : G , f * g * f⁻¹ = 1) : g = 1 := by
  rcases h with ⟨f,hf⟩
  have h1 : f⁻¹ * (f * g * f⁻¹) * f = 1 := by simp only [hf, mul_one, mul_left_inv]
  have h2 : f⁻¹ * (f * g * f⁻¹) * f = g := by group
  rw [← h2,h1]


example {G : Type*} [Group G] (f g h : G) : ∃ x : G , f * x * g = h := by
  use f⁻¹ * h * g⁻¹
  group

example {G : Type*} [Group G] (x y : G) : x * y = y * x → x * y * x⁻¹ * y⁻¹ = 1 := by
  intro h
  simp only [h,mul_inv_cancel_right, mul_right_inv]

example {G : Type*} [Group G] (x y : G) : x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
  intro h
  have : x * y * x⁻¹ * y⁻¹ * y * x = y * x := by
    simp only [h,one_mul]
  simp only [inv_mul_cancel_right,inv_mul_cancel_right] at this
  exact this

example {G : Type*} [Group G] (x y : G) : x * y * x⁻¹ * y⁻¹ = 1 ↔ x * y = y * x := by
  constructor
  · intro h
    have : x * y * x⁻¹ * y⁻¹ * y * x = y * x := by
      simp only [h,one_mul]
    simp only [inv_mul_cancel_right,inv_mul_cancel_right] at this
    exact this
  · intro h
    simp only [h,mul_inv_cancel_right, mul_right_inv]

theorem bool_ring1 {R : Type*} [Ring R] (h : ∀ a : R , a * a = a) : ∀ a : R , a = -a := by
  intro a
  have h1: (a + a) * (a + a) = a + a + a + a := by
    calc
      _= a * a + a * a + a * a + a * a := by
        simp only[mul_add,add_mul,add_assoc]
      _=_ := by rw [h a]
  rw [h (a + a)] at h1
  calc
    _= a + a + a + a + (-a) + (-a) + (-a) := by simp only [add_neg_cancel_right]
    _= a + a + (-a) + (-a) + (-a) := by rw [←h1]
    _=_ := by simp only [add_neg_cancel_right, add_right_neg, zero_add]

def bool_ring2 {R : Type*} [hR : Ring R] (h : ∀ a : R , a * a = a) : CommRing R := {
  hR with
  mul_comm := by
    intro a b
    have : b * a + a * b = 0 := by
      calc
        _= a + b * a + a * b + b + (-a) + (-b) := by abel
        _= a * a + b * a + a * b + b * b + (-a) + (-b) := by rw [h a,h b]
        _= (a + b) * (a + b) + (-a) + (-b) := by simp only [add_left_inj,add_mul,mul_add,add_assoc]
        _=_ := by simp only [h (a + b), add_neg_cancel_comm, add_right_neg]
    calc
      _= -(b * a) + (b * a + a * b) := by simp only [neg_add_cancel_left]
      _= -(b * a) := by simp [this]
      _=_ := by symm;apply bool_ring1 h
}

example {R : Type*} [hR : Ring R] (h : ∀ a : R , a * a * a = a) : CommRing R := {
  hR with
  mul_comm := by
    intro a b
    have h1: b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b = 0 := by
      calc
        _= a + b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b + b + (-a) + (-b) := by abel
        _= a * a * a + b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b + b * b * b + (-a) + (-b) := by rw[h a,h b]
        _= (a + b) * (a + b) * (a + b) + (-a) + (-b) := by simp [add_mul,mul_add];abel
        _=_ := by simp only [h (a + b), add_neg_cancel_comm, add_right_neg]
    have h2: -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b = 0 := by
      calc
       _= a + -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b + (-b) + (-a) + b := by abel
       _= a * a * a + -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b + (-b) * (-b) * (-b) + (-a) + b := by rw [h a,h (-b)]
       _= (a - b) * (a - b) * (a - b) + (-a) + b := by simp only [sub_mul,mul_sub,mul_neg, neg_mul, neg_neg, add_left_inj];abel
       _=_ := by simp only [h (a - b)];abel
    have h3 : b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b = 0 := by
      calc
        _= b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b - (-(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b) := by abel
        _=_ := by simp only [h1, h2, sub_self]
    have h4 : a * b + a * a * b * a + a * b * a * a + a * b + a * a * b * a + a * b * a * a = 0 := by
      calc
        _= a * a * a * b + a * a * b * a + a * b * a * a + a * a * a * b + a * a * b * a + a * b * a * a := by simp only [h a]
        _= a * (b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b) := by simp only [mul_add,mul_assoc];abel
        _=_ := by simp only [h3, mul_zero]
    have h5 : b * a + a * a * b * a + a * b * a * a + b * a + a * a * b * a + a * b * a * a = 0 := by
      calc
        _= b * (a * a * a) + a * a * b * a + a * b * a * a + b * (a * a * a) + a * a * b * a + a * b * a * a := by simp only [h a]
        _= (b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b) * a := by simp only [add_mul,mul_assoc];abel
        _=_ := by simp only [h3, zero_mul]
    have comm2 : a * b - b * a + a * b - b * a = 0 := by
      calc
        _= (a * b + a * a * b * a + a * b * a * a + a * b + a * a * b * a + a * b * a * a) - (b * a + a * a * b * a + a * b * a * a + b * a + a * a * b * a + a * b * a * a) := by abel
        _=_ := by simp only [h4, h5, sub_self]
    have h6 : ∀ x : R, x + x + x + x * x + x * x + x * x = 0 := by
      intro x
      calc
        _= x + x + x + x + x * x + x * x + x * x + x * x - (x + x * x) := by abel
        _= x * x * x + x * x * x * x * x + x * x * x * x * x + x * x * x * x * x + x * x * x * x + x * x * x * x + x * x * x * x + x * x * x * x * x * x - (x + x * x) := by simp only [h x]
        _= (x + x * x) * (x + x * x) * (x + x * x) - (x + x * x) := by simp [mul_add,add_mul,mul_assoc];abel
        _=_ := by simp only [h (x + x * x), sub_self]
    have char6 :  ∀ x : R, x + x + x + x + x + x = 0 := by
      intro x
      calc
        _= (x + x) * (x + x) * (x + x) - x - x := by simp only [add_mul,mul_add,←mul_assoc,h x];abel
        _=_ := by simp only [h (x + x), add_sub_cancel_right, sub_self]
    have comm3 : a * b - b * a + a * b - b * a + a * b - b * a = 0 := by
      calc
        _= a * b + b * a + a * b + b * a + a * b + b * a - (b * a + b * a + b * a + b * a + b * a + b * a) := by abel
        _= a * b + b * a + a * b + b * a + a * b + b * a := by simp only [char6, sub_zero]
        _= ((a + b) + (a + b) + (a + b) + (a + b) * (a + b) + (a + b) * (a + b) + (a + b) * (a + b)) - (a + a + a + a * a + a * a + a * a) - (b + b + b + b * b + b * b + b * b) := by simp only [mul_add,add_mul];abel
        _=_ := by simp only [h6, sub_self]
    have comm : a * b - b * a = 0 := by rw [←comm3,comm2, zero_add]
    calc
      _= a * b - (a * b - b * a) := by simp only [comm, sub_zero]
      _=_ := by abel
}
