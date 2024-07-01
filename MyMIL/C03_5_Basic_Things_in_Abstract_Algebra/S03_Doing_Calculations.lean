import Mathlib

section Calculations_in_Rings

theorem bool_ring1 {R : Type*} [Ring R] (h : ∀ a : R, a * a = a) : ∀ a : R, a = -a := by
  intro a
  have h1: (a + a) * (a + a) = a + a + a + a := by
    calc
      _= a * a + a * a + a * a + a * a := by
        simp only [mul_add, add_mul, add_assoc]
      _=_ := by rw [h a]
  rw [h (a + a)] at h1
  calc
    _= a + a + a + a + (-a) + (-a) + (-a) := by simp only [add_neg_cancel_right]
    _= a + a + (-a) + (-a) + (-a) := by rw [← h1]
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
    -- (a + b) ^ 3 - a ^ 3 - b ^ 3 = 0
    -- baa + aba + aab + bba + bab + abb = 0
    have h1: b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b = 0 := by
      calc
        _= a + b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b + b + (-a) + (-b) := by abel
        _= a * a * a + b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b + b * b * b + (-a) + (-b) := by rw [h a, h b]
        _= (a + b) * (a + b) * (a + b) + (-a) + (-b) := by simp only [mul_add, add_mul, add_left_inj]; abel
        _=_ := by simp only [h (a + b), add_neg_cancel_comm, add_right_neg]
    -- (a - b) ^ 3 - a ^ 3 + b ^ 3 = 0
    -- - (baa + aba + aab) + (bba + bab + abb) = 0
    have h2: -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b = 0 := by
      calc
       _= a + -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b + (-b) + (-a) + b := by abel
       _= a * a * a + -(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b + (-b) * (-b) * (-b) + (-a) + b := by rw [h a, h (-b)]
       _= (a - b) * (a - b) * (a - b) + (-a) + b := by simp only [sub_mul, mul_sub, mul_neg, neg_mul, neg_neg, add_left_inj]; abel
       _=_ := by simp only [h (a - b)]; abel
    -- 2 * (baa + aba + aab) = 0
    have h3 : b * a * a + a * b * a + a * a * b + b * a * a + a * b * a + a * a * b = 0 := by
      calc
        _= b * a * a + a * b * a + b * b * a + a * a * b + b * a * b + a * b * b - (-(b * a * a) + -(a * b * a) + b * b * a + -(a * a * b) + b * a * b + a * b * b) := by abel
        _=_ := by simp only [h1, h2, sub_self]
    -- a * 2 * (baa + aba + aab) - 2 * (baa + aba + aab) * a = 0
    -- 2 *（ab - ba）= 0
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
    -- (x + x ^ 2) ^ 3 - (x + x ^ 2) = 0
    -- 3 * (x + x ^ 2) = 0
    have h6 : ∀ x : R, x + x + x + x * x + x * x + x * x = 0 := by
      intro x
      calc
        _= x + x + x + x + x * x + x * x + x * x + x * x - (x + x * x) := by abel
        _= x * x * x + x * x * x * x * x + x * x * x * x * x + x * x * x * x * x + x * x * x * x + x * x * x * x + x * x * x * x + x * x * x * x * x * x - (x + x * x) := by simp only [h x]
        _= (x + x * x) * (x + x * x) * (x + x * x) - (x + x * x) := by simp [mul_add, add_mul, mul_assoc]; abel
        _=_ := by simp only [h (x + x * x), sub_self]
    -- (x + x) ^ 3 - (x + x) = 0
    -- 6 * x = 0
    have char6 :  ∀ x : R, x + x + x + x + x + x = 0 := by
      intro x
      calc
        _= (x + x) * (x + x) * (x + x) - x - x := by simp only [add_mul, mul_add, ←mul_assoc, h x]; abel
        _=_ := by simp only [h (x + x), add_sub_cancel_right, sub_self]
    -- 3 * ((a + b) + (a + b) ^ 2) - 3 * (a + a ^ 2) - 3 * (b + b ^ 2) - 6 * ba = 0
    -- 3 * (ab - ba) = 0
    have comm3 : a * b - b * a + a * b - b * a + a * b - b * a = 0 := by
      calc
        _= a * b + b * a + a * b + b * a + a * b + b * a - (b * a + b * a + b * a + b * a + b * a + b * a) := by abel
        _= a * b + b * a + a * b + b * a + a * b + b * a := by simp only [char6, sub_zero]
        _= ((a + b) + (a + b) + (a + b) + (a + b) * (a + b) + (a + b) * (a + b) + (a + b) * (a + b)) - (a + a + a + a * a + a * a + a * a) - (b + b + b + b * b + b * b + b * b) := by simp only [mul_add, add_mul]; abel
        _=_ := by simp only [h6, sub_self]
    -- 3 * (ab - ba) = 0, 2 * (ab - ba) = 0
    -- ab - ba = 0
    have comm : a * b - b * a = 0 := by rw [← comm3, comm2, zero_add]
    calc
      _= a * b - (a * b - b * a) := by simp only [comm, sub_zero]
      _=_ := by abel
}

-- See https://math.stackexchange.com/questions/2589276/the-ring-r-that-satisfying-xn-x if you want to know more about this.
example {R : Type*} [hR : Ring R] (n : ℕ) (hnge2 : n ≥ 2) (h : ∀ x : R, x ^ n = x) : CommRing R := by sorry

end Calculations_in_Rings


section Dihedral_Groups
-- The examples are from Mathlib.GroupTheory.SpecificGroups.Dihedral
variable (n : ℕ) [NeZero n]
#check DihedralGroup n

#check DihedralGroup.r_mul_r
#check DihedralGroup.r_mul_sr
#check DihedralGroup.sr_mul_r
#check DihedralGroup.sr_mul_sr
#check DihedralGroup.one_def

#check ZMod.val

theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  have correspondence : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n := {
    toFun := fun x ↦ (
      match x with
      | Sum.inl i => DihedralGroup.r i
      | Sum.inr i => DihedralGroup.sr i
    )
    invFun := fun x ↦ (
      match x with
      | DihedralGroup.r i => Sum.inl i
      | DihedralGroup.sr i => Sum.inr i
    )
    left_inv := fun x ↦ (
      match x with
      | Sum.inl i => by simp only
      | Sum.inr i => by simp only
    )
    right_inv := fun x ↦ (
      match x with
      | DihedralGroup.r i => by simp only
      | DihedralGroup.sr i => by simp only
    )
  }
  rw [← Fintype.card_eq.mpr ⟨correspondence⟩]
  simp only [Fintype.card_sum, ZMod.card, two_mul]

theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (DihedralGroup.r i : DihedralGroup n) = n / Nat.gcd n i.val := by
  have r_1_pow (u : ℕ): (DihedralGroup.r 1) ^ u = DihedralGroup.r (u : ZMod n) := by
    induction' u with u ih
    · rw [pow_zero, DihedralGroup.one_def]
      simp only [Nat.cast_zero]
    · rw [pow_add (DihedralGroup.r 1) u 1, ih, pow_one, DihedralGroup.r_mul_r]
      simp only [Nat.cast_add, Nat.cast_one]
  have order_r_1 : orderOf (DihedralGroup.r 1 : DihedralGroup n) = n := by
    have pow_eq_1 : (DihedralGroup.r 1 : DihedralGroup n) ^ n = 1 := by
      rw [r_1_pow, DihedralGroup.one_def]
      congr 1
      simp only [CharP.cast_eq_zero]
    apply le_antisymm
    · apply orderOf_le_of_pow_eq_one (NeZero.pos n) pow_eq_1
    · set u := orderOf (DihedralGroup.r 1 : DihedralGroup n) with hu
      have : (DihedralGroup.r 1 : DihedralGroup n) ^ u = 1 := pow_orderOf_eq_one (DihedralGroup.r 1 : DihedralGroup n)
      rw [r_1_pow, DihedralGroup.one_def] at this
      simp only [DihedralGroup.r.injEq] at this
      have : n ∣ u := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd u n).mp this
      apply PNat.le_of_dvd (m := ⟨n, NeZero.pos n⟩) (n := ⟨u, by
        apply Nat.pos_of_ne_zero
        by_contra h'
        rw [hu] at h'
        have : _ := orderOf_eq_zero_iff'.mp h'
        exact this n (NeZero.pos n) pow_eq_1
        ⟩) (by exact PNat.dvd_iff.mpr this)
  have : i = ((i.val) : ZMod n) := by exact Eq.symm (ZMod.natCast_zmod_val i)
  rw [this, ← (r_1_pow i.val), orderOf_pow, order_r_1, ← this]

theorem card_commute_odd (hn : Odd n) : Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3) := by
  set u : ℕ := (n + 1) / 2 with u_def
  have two_mul_ker_triv (x : ZMod n) (h : 2 * x = 0) : x = 0 := by
    calc
    _ = (1 : ZMod n) * x := by rw [one_mul]
    _ = ((n + 1) : ZMod n) * x := by simp only [one_mul, CharP.cast_eq_zero, zero_add]
    _ = (((u * 2) : ℕ) : ZMod n) * x := by
      congr
      have : u * 2 = n + 1 := by
        rw [u_def, eq_comm]
        exact (Nat.div_eq_iff_eq_mul_left (a := (n + 1)) (b := 2) (c := (n + 1) / 2) (by norm_num) (by rcases hn with ⟨v, hv⟩; rw [hv, Nat.dvd_add_self_right]; exact dvd_mul_right 2 v )).mp rfl
      simp only [CharP.cast_eq_zero, zero_add, this, Nat.cast_add, Nat.cast_one]
    _ = ((u : ZMod n) * (2 : ZMod n)) * x := by simp only [Nat.cast_mul, Nat.cast_ofNat]
    _ = (u : ZMod n) * ((2 : ZMod n) * x) := by rw [mul_assoc]
    _ = 0 := by rw [h, mul_zero]
  have correspondence : { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃ (ZMod n) ⊕ (ZMod n) ⊕ (ZMod n) ⊕ ((ZMod n) × (ZMod n)) :=
    { toFun := fun x ↦ (
        match x with
        | ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
        | ⟨⟨DihedralGroup.r i, DihedralGroup.sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl j))
        | ⟨⟨DihedralGroup.sr i, DihedralGroup.r j⟩, _⟩ => Sum.inr (Sum.inl i)
        | ⟨⟨DihedralGroup.sr i, DihedralGroup.sr j⟩, _⟩ => Sum.inl i
      )
      invFun := fun x ↦ (
        match x with
        | Sum.inl i => ⟨⟨DihedralGroup.sr i, DihedralGroup.sr i⟩, rfl⟩
        | Sum.inr (Sum.inl i) => ⟨⟨DihedralGroup.sr i, DihedralGroup.r 0⟩, by
            show DihedralGroup.sr (i + 0) = DihedralGroup.sr (i - 0)
            simp only [add_zero, sub_zero]⟩
        | Sum.inr (Sum.inr (Sum.inl j)) => ⟨⟨DihedralGroup.r 0, DihedralGroup.sr j⟩, by
            show DihedralGroup.sr (j - 0) = DihedralGroup.sr (j + 0)
            simp only [sub_zero, add_zero]⟩
        | Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩)) => ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, by
            show DihedralGroup.r (i + j) = DihedralGroup.r (j + i)
            rw [add_comm]⟩
      )
      left_inv := fun x ↦ (
        match x with
        | ⟨⟨DihedralGroup.r i, DihedralGroup.r j⟩, _⟩ => by simp only
        | ⟨⟨DihedralGroup.r i, DihedralGroup.sr j⟩, hcomm⟩ => by
            simp only [Subtype.mk.injEq, Prod.mk.injEq, DihedralGroup.r.injEq, and_true]
            have : DihedralGroup.sr (j - i) = DihedralGroup.sr (j + i) := hcomm
            simp only [DihedralGroup.sr.injEq] at this
            have : 2 * i = 0 := by
              rw [← sub_self (j + i)]
              nth_rw 2 [← this]
              rw [add_sub_sub_cancel, two_mul]
            rw [two_mul_ker_triv i this]
        | ⟨⟨DihedralGroup.sr i, DihedralGroup.r j⟩, hcomm⟩ => by
            simp only [Subtype.mk.injEq, Prod.mk.injEq, DihedralGroup.r.injEq, true_and]
            have : DihedralGroup.sr (i + j) = DihedralGroup.sr (i - j) := hcomm
            simp only [DihedralGroup.sr.injEq] at this
            have : 2 * j = 0 := by
              rw [← sub_self (i + j)]
              nth_rw 2 [this]
              rw [add_sub_sub_cancel, two_mul]
            rw [two_mul_ker_triv j this]
        | ⟨⟨DihedralGroup.sr i, DihedralGroup.sr j⟩, hcomm⟩ => by
            simp only [Subtype.mk.injEq, Prod.mk.injEq, DihedralGroup.sr.injEq, true_and]
            have : DihedralGroup.r (j - i) = DihedralGroup.r (i - j) := hcomm
            simp only [DihedralGroup.r.injEq] at this
            have : 2 * (j - i) = 0 := by
              rw [two_mul]
              nth_rw 1 [this]
              ring
            have : _ := two_mul_ker_triv (j - i) this
            rw [← sub_zero j, ← sub_self i, ← sub_add, this, zero_add]
      )
      right_inv := fun x ↦ (
        match x with
        | Sum.inl i => rfl
        | Sum.inr (Sum.inl i) => rfl
        | Sum.inr (Sum.inr (Sum.inl j)) => rfl
        | Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩)) => rfl
      ) }
  rw [Nat.card_congr correspondence]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card, Fintype.card_prod]
  ring

end Dihedral_Groups
