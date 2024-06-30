import Mathlib

section Calculations_in_Rings

theorem bool_ring1 {R : Type*} [Ring R] (h : ∀ a : R, a * a = a) : ∀ a : R, a = -a := by
  intro a
  have h1: (a + a) * (a + a) = a + a + a + a := by
    calc
      _= a * a + a * a + a * a + a * a := by
        simp only[mul_add, add_mul, add_assoc]
      _=_ := by rw [h a]
  rw [h (a + a)] at h1
  calc
    _= a + a + a + a + (-a) + (-a) + (-a) := by simp only [add_neg_cancel_right]
    _= a + a + (-a) + (-a) + (-a) := by rw [←h1]
    _=_ := by simp only [add_neg_cancel_right, add_right_neg, zero_add]

def bool_ring2 {R : Type*} [hR : Ring R] (h : ∀ a : R, a * a = a) : CommRing R := {
  hR with
  mul_comm := by
    intro a b
    have : b * a + a * b = 0 := by
      calc
        _= a + b * a + a * b + b + (-a) + (-b) := by abel
        _= a * a + b * a + a * b + b * b + (-a) + (-b) := by rw [h a, h b]
        _= (a + b) * (a + b) + (-a) + (-b) := by simp only [add_left_inj, add_mul, mul_add, add_assoc]
        _=_ := by simp only [h (a + b), add_neg_cancel_comm, add_right_neg]
    calc
      _= -(b * a) + (b * a + a * b) := by simp only [neg_add_cancel_left]
      _= -(b * a) := by simp [this]
      _=_ := by symm; apply bool_ring1 h
}

example {R : Type*} [hR : Ring R] (h : ∀ a : R, a * a * a = a) : CommRing R := {
  hR with
  mul_comm := by
    intro a b
    have h1: b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b = 0 := by
      calc
        _= a + b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b + b + (-a) + (-b) := by abel
        _= a * a * a + b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b + b * b * b + (-a) + (-b) := by rw[h a, h b]
        _= (a + b) * (a + b) * (a + b) + (-a) + (-b) := by simp [add_mul, mul_add]; abel
        _=_ := by simp only [h (a + b), add_neg_cancel_comm, add_right_neg]
    have h2: -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b = 0 := by
      calc
       _= a + -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b + (-b) + (-a) + b := by abel
       _= a * a * a + -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b + (-b) * (-b) * (-b) + (-a) + b := by rw [h a, h (-b)]
       _= (a - b) * (a - b) * (a - b) + (-a) + b := by simp only [sub_mul, mul_sub, mul_neg, neg_mul, neg_neg, add_left_inj]; abel
       _=_ := by simp only [h (a - b)]; abel
    have h3 : b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b = 0 := by
      calc
        _= b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b - (-(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b) := by abel
        _=_ := by simp only [h1, h2, sub_self]
    have h4 : a * b + a * a * b * a + a * b * a * a + a * b + a * a * b * a + a * b * a * a = 0 := by
      calc
        _= a * a * a * b + a * a * b * a + a * b * a * a + a * a * a * b + a * a * b * a + a * b * a * a := by simp only [h a]
        _= a * (b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b) := by simp only [mul_add, mul_assoc]; abel
        _=_ := by simp only [h3, mul_zero]
    have h5 : b * a + a * a * b * a + a * b * a * a + b * a + a * a * b * a + a * b * a * a = 0 := by
      calc
        _= b * (a * a * a) + a * a * b * a + a * b * a * a + b * (a * a * a) + a * a * b * a + a * b * a * a := by simp only [h a]
        _= (b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b) * a := by simp only [add_mul, mul_assoc]; abel
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
        _= (x + x * x) * (x + x * x) * (x + x * x) - (x + x * x) := by simp [mul_add, add_mul, mul_assoc]; abel
        _=_ := by simp only [h (x + x * x), sub_self]
    have char6 :  ∀ x : R, x + x + x + x + x + x = 0 := by
      intro x
      calc
        _= (x + x) * (x + x) * (x + x) - x - x := by simp only [add_mul, mul_add, ←mul_assoc, h x]; abel
        _=_ := by simp only [h (x + x), add_sub_cancel_right, sub_self]
    have comm3 : a * b - b * a + a * b - b * a + a * b - b * a = 0 := by
      calc
        _= a * b + b * a + a * b + b * a + a * b + b * a - (b * a + b * a + b * a + b * a + b * a + b * a) := by abel
        _= a * b + b * a + a * b + b * a + a * b + b * a := by simp only [char6, sub_zero]
        _= ((a + b) + (a + b) + (a + b) + (a + b) * (a + b) + (a + b) * (a + b) + (a + b) * (a + b)) - (a + a + a + a * a + a * a + a * a) - (b + b + b + b * b + b * b + b * b) := by simp only [mul_add, add_mul]; abel
        _=_ := by simp only [h6, sub_self]
    have comm : a * b - b * a = 0 := by rw [← comm3, comm2, zero_add]
    calc
      _= a * b - (a * b - b * a) := by simp only [comm, sub_zero]
      _=_ := by abel
}

-- See https://math.stackexchange.com/questions/2589276/the-ring-r-that-satisfying-xn-x if you want to know more about this.
example {R : Type*} [hR : Ring R] (n : ℕ) (hnge2 : n ≥ 2) (h : ∀ x : R, x ^ n = x) : CommRing R := by sorry

end Calculations_in_Rings


section Dihedral_Groups



end Dihedral_Groups
