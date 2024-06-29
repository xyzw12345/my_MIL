import Mathlib

section Axioms_of_Groups

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  rw [← one_mul (a * a⁻¹)]
  nth_rw 1 [← mul_left_inv (a * a⁻¹)]
  rw [mul_assoc, mul_assoc, ← mul_assoc a⁻¹, mul_left_inv, one_mul, mul_left_inv]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← mul_left_inv a, ← mul_assoc, mul_right_inv a, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_one (b⁻¹ * a⁻¹), ← mul_right_inv (a * b), ← mul_assoc, mul_assoc b⁻¹, ← mul_assoc a⁻¹, mul_left_inv, one_mul, mul_left_inv, one_mul]

end MyGroup

end Axioms_of_Groups

section How_To_Define_a_Group

-- Things introduced here will be further elaborated later this week.

end How_To_Define_a_Group

section From_SemiGroup_To_Group

noncomputable example {G : Type*} [Semigroup G] [h_nonempty : Nonempty G] (h : ∀ a b : G, (∃ x : G, x * a = b) ∧ (∃ y : G, a * y = b)) : Group G := by
  let u := Classical.choice h_nonempty
  -- rcases h_nonempty with ⟨u⟩
  let e1 := Classical.choose (h u u).1
  have h_e1 : e1 * u = u := by
    exact Classical.choose_spec (h u u).1
  let e2 := Classical.choose (h u u).2
  have h_e2 : u * e2 = u := by
    exact Classical.choose_spec (h u u).2
  have heq : e1 = e2 := by
    rcases (h u e2).2 with ⟨x, hx⟩
    rcases (h u e1).1 with ⟨y, hy⟩
    rw [← hy, ← h_e2, ← mul_assoc, hy, ← hx, ← mul_assoc, h_e1]
  exact {
    one := e1,
    one_mul := (by
      intro g
      show e1 * g = g
      rcases (h u g).2 with ⟨z, hz⟩
      rw [← hz, ← mul_assoc, h_e1]
    ),
    mul_one := (by
      intro g
      show g * e1 = g
      rcases (h u g).1 with ⟨z, hz⟩
      rw [← hz, mul_assoc, heq, h_e2]
    ),
    inv := (
      fun y ↦ Classical.choose (h y e1).1
    ),
    mul_left_inv := (by
      intro g
      show Classical.choose (h g e1).1 * g = e1
      exact Classical.choose_spec (h g e1).1
    )
  }

/-
The following example is from
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/how.20to.20specify.20an.20.20identity.20for.20a.20semigroup.20.3F
-/
noncomputable example {G : Type*} [Semigroup G] [h_nonempty : Nonempty G] (h : ∀ (x : G), ∃! (y : G), x * y * x = x) : Group G := by
  have fun_is_pairing (x y : G) (h1 : x * y * x = x) : y * x * y = y := by
    apply ExistsUnique.unique (h x)
    · rw [← mul_assoc, ← mul_assoc, h1, h1]
    · exact h1
  have mul_pair_idem (x y : G) (h1 : x * y * x = x) : (x * y) * (x * y) = (x * y) := by rw [← mul_assoc, h1]
  have h_idem_is_identity (i : G) (hi : i * i = i) : ∀ (g : G), (i * g = g) ∧ (g * i = g) := by
    intro g
    let g1 := Classical.choose (h (i * g * i))
    have : (i * g * i) * g1 * (i * g * i) = (i * g * i) := by exact (Classical.choose_spec (h (i * g * i))).1
    have hh1 : g1 * (i * g * i) * g1 = g1 := fun_is_pairing (i * g * i) g1 this
    have hh2 : i * g1 * i = g1 := by
      apply ExistsUnique.unique (h (i * g * i)) _ this
      -- nth_rw 2 [← hi] at this
      -- nth_rw 4 [← hi] at this
      -- group at this
      -- group
      -- exact this
      rw [← mul_assoc, mul_assoc i g _, mul_assoc i (g * i) _, mul_assoc, mul_assoc g i _, ← mul_assoc i (i * g1) _, ← mul_assoc i i g1, hi, ← mul_assoc i g (i * g1 * i), mul_assoc i g1 i, ← mul_assoc (i * g) , mul_assoc (i * g * i), mul_assoc g1 i _, ← mul_assoc i (i * g), ← mul_assoc i i _, hi, ← mul_assoc (i * g * i), ← mul_assoc i g i, this]
    have hh3 : (i * g1 * i) * (i * g * i) * (i * g1 * i) = (i * g1 * i) := by rw [hh2, hh1]
    have hh4 : i * g * i = g := by
      apply ExistsUnique.unique (h (i * g1 * i)) hh3 _
      nth_rw 2 [← hi]
      nth_rw 4 [← hi]
      -- group at hh3
      -- group
      -- exact hh3
      rw [mul_assoc i i g1, mul_assoc i (i * g1), ← mul_assoc, ← hh3]
      congr 1
      rw [← mul_assoc (i * g1) i i, mul_assoc _ g i, mul_assoc _ i (g * i), ← mul_assoc i g i]
    have hh5 : i * g * i = g * i := by
      apply ExistsUnique.unique (h (i * g1 * i)) hh3 _
      nth_rw 2 [← hi]
      rw [← hh3]
      congr 1
      -- group
      rw [← mul_assoc (i * g1) i i, mul_assoc _ g i, mul_assoc _ i (g * i), ← mul_assoc i g i]
    have hh6 : i * g * i = i * g := by
      apply ExistsUnique.unique (h (i * g1 * i)) hh3 _
      nth_rw 4 [← hi]
      nth_rw 2 [← hh3]
      -- group
      rw [mul_assoc (i * i) g1 i, mul_assoc i i (g1 * i), ← mul_assoc _ i (i * (g1 * i)), ← mul_assoc i g1 i]
      congr 1
      rw [mul_assoc _ (i * g) i]
    exact ⟨Eq.trans hh6.symm hh4, Eq.trans hh5.symm hh4⟩
  let x := Classical.choice h_nonempty
  let y := Classical.choose (h x)
  have hxy : x * y * x = x := by exact (Classical.choose_spec (h x)).1
  let e := x * y
  have e_idem : e * e = e := by exact mul_pair_idem x y hxy
  exact {
    one := e,
    one_mul := fun g ↦ (h_idem_is_identity e e_idem g).1,
    mul_one := fun g ↦ (h_idem_is_identity e e_idem g).2,
    inv := fun g ↦ Classical.choose (h g),
    mul_left_inv := (by
      intro g
      let g1 := Classical.choose (h g)
      show g1 * g = e
      have : g * g1 * g = g := by exact (Classical.choose_spec (h g)).1
      have : g1 * g * g1 = g1 := fun_is_pairing g g1 this
      let e' := g1 * g
      show e' = e
      have : e' * e' = e' := mul_pair_idem g1 g this
      rw [← (h_idem_is_identity e e_idem e').1, (h_idem_is_identity e' this e).2]
    )
  }
