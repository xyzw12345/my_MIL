import Mathlib
-- /-
-- 14.
-- Suppose that $n$ is a positive integer, prove that all nth roots of unity form a cyclic group of order $n$ under the normal multiplication of complex numbers.
-- -/
-- #check Nat.coprime_one_left_eq_true
-- #check orderOf_eq_card_of_forall_mem_zpowers

-- theorem exercise14 {n : PNat} : IsCyclic (rootsOfUnity n ℂ) ∧ Nat.card (rootsOfUnity n ℂ) = n := by
--   have : IsCyclic (rootsOfUnity n ℂ) := by infer_instance
--   constructor
--   · exact this
--   · rcases this with ⟨g, hg⟩
--     have : orderOf g = n := by
--       apply dvd_antisymm
--       · apply orderOf_dvd_of_pow_eq_one
--         ext : 1
--         simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
--         rw [← (mem_rootsOfUnity n (g : ℂˣ))]
--         exact g.2
--       · have : _ := Complex.isPrimitiveRoot_exp_of_coprime 1 n.val (ne_of_gt n.2) (by simp only [Nat.coprime_one_left_eq_true])
--         sorry
--     sorry






/-
49.
Suppose $A, B$ are two subgroups of group $G$ and that $G = AB$, if subgroup $C$ contains $A$, then $C = A(B \cap C)$.

Proof:
For $c \in C$, because that $G = AB$ and $c \in G$, there exists $a \in A$ and $b \in B$ such that $c = ab$.
It suffices to prove that $b \in (B \cap C)$.
Since $c = ab$, we have that $b = a^{-1} c$.
Because $a \in A \subeq C$ and $C$ is a subgroup of G, we have $a^{-1} \in C$.
Therefore, $b = a^{-1} c \in C$.
-/

theorem exercise_49 (G : Type u) [self : Group G] (A B : Subgroup G) (h : ∀ g : G, (∃ (a : A) (b : B), g = a * b)) (C : Subgroup G) (hac : A ≤ C) : ∀ c : C, ∃ (a : A) (b : B) (_ : (b : G) ∈ (B ⊓ C)), (c : G) = a * b := by
  -- For $c \in C$, because that $G = AB$ and $c \in G$, there exists $a \in A$ and $b \in B$ such that $c = ab$.
  rintro c; rcases (h c) with ⟨a, b, heq⟩
  have : (b : G) ∈ B := by simp only [SetLike.coe_mem]
  -- It suffices to prove that $b \in (C)$.
  suffices h : ((b : G) ∈ C) by exact ⟨a, b, ⟨⟨by assumption, by assumption⟩, heq⟩⟩
  -- Since $c = ab$, we have that $b = a^{-1} c$.
  have hbeq : (b : G) = a⁻¹ * (c : G) := by
    calc
    _= (a⁻¹ : G) * (a : G) * (b : G) := by group
    _= (a⁻¹ : G) * ((a : G) * (b : G)) := by group
    _= (a⁻¹ : G) * (c : G) := by rw [heq]
  -- Because $a \in A \subeq C$ and $C$ is a subgroup of G, we have $a^{-1} \in C$.
  have : (a⁻¹ : G) ∈ A := by apply (Subgroup.inv_mem_iff A).mpr _; simp only [SetLike.coe_mem]
  have : (a⁻¹ : G) ∈ C := by exact hac this
  -- Therefore, $b = a^{-1} c \in C$.
  rw [hbeq]; exact C.mul_mem this (by simp only [SetLike.coe_mem])

/-
120.
Let $G$ be the set ${(a, b) \in \mathbb{R}^2 | a \ne 0}$, define $(a, b) * (c, d) = (a * c, a * d + b)$ on $G$. Prove that $(G, *)$ is a group.
Proof:
The associativity of multiplication could be directly verified via calculation.
Take the unit of $G$ to be $(1, 0)$.
The fact that $(1, 0)$ satisfies the axioms for unit can be verified through direct calculation.
Take the inverse of $(x, y)$ to be $(x^{-1}, - x^{-1} y)$.
The fact that this element satisfies the axiom for an inverse can be verified through direct calculation.
-/

def G := {x : ℝ × ℝ | x.1 ≠ (0 : ℝ)}

noncomputable instance : Group G where
  mul x y := ⟨⟨x.1.1 * y.1.1, x.1.1 * y.1.2 + x.1.2⟩, mul_ne_zero x.2 y.2⟩
  -- The associativity of multiplication could be directly verified via calculation.
  mul_assoc x y z := by
    ext;
    · exact mul_assoc x.1.1 y.1.1 z.1.1
    · show (x.1.1 * y.1.1) * z.1.2 + (x.1.1 * y.1.2 + x.1.2) = x.1.1 * (y.1.1 * z.1.2 + y.1.2) + x.1.2; ring
  -- Take the unit of $G$ to be $(1, 0)$.
  one := ⟨⟨1, 0⟩, by show 1 ≠ 0; norm_num⟩
  -- The fact that $(1, 0)$ satisfies the axioms for unit can be verified through direct calculation.
  one_mul x := by
    ext;
    · exact one_mul x.1.1
    · show 1 * x.1.2 + 0 = x.1.2; ring
  mul_one x := by
    ext;
    · exact mul_one x.1.1
    · show x.1.1 * 0 + x.1.2 = x.1.2; ring
  -- Take the inverse of $(x, y)$ to be $(x^{-1}, - x^{-1} y)$.
  inv x := ⟨⟨x.1.1⁻¹, - x.1.1⁻¹ * x.1.2⟩, inv_ne_zero x.2⟩
  -- The fact that this element satisfies the axiom for an inverse can be verified through direct calculation.
  mul_left_inv x := by
    ext;
    · show x.1.1⁻¹ * x.1.1 = 1; exact (inv_mul_eq_one₀ x.2).mpr (by rfl)
    · show x.1.1⁻¹ * x.1.2 + (- x.1.1⁻¹ * x.1.2) = 0
      simp only [neg_mul, add_right_neg]

/-
127.
Suppose $G$ is a group and $g \in G$, with $o(g) = m n, gcd(m, n) = 1$. Then there exists $a, b \in G$ such that $g = a b, o(a) = m, o(b) = n$ and $a, b$ are powers of $g$.

Proof:
Since $gcd(m, n) = 1$, by Bezout's theorem, there exists $u, v \in \mathbb{Z}$, such that $n * u + m * v = 1$.
Now take $a = g ^ {n u}, b = g ^ {m v}$.

Then $g = a b$ holds trivially.

To prove that $o(a) = m$, it suffices to show that $a^{m} = 1$ and that there is no other natural number $m1$ such that $0 < m1 < m$ and $a ^ {m1} = 1$.
$a^{m} = 1$ holds trivially.
Assume the contrary, that there exists an natural number $m1$ such that $0 < m1 < m$ and $a ^ {m1} = 1$.
Then, $g ^ {n * m1} = g ^ {n * m1 * (n * u + m * v)} = g ^ {n * m1 * n * u} * g ^ {n * m1 * m * v} = ((g ^ {n * u * m1}) ^ n * (g ^ {n * m}) ^ {m1 * v} = 1$.But $0 < n * m1 < m * n$, which yields a contradiction with the condition that $o(g) = m n$.

To prove that $o(b) = n$, it suffices to show that $b ^ {n} = 1$ and that there is no other natural number $n1$ such that $0 < n1 < n$ and $b ^ {n1} = 1$.
$b ^ {n} = 1$ holds trivially.
Assume the contrary, that there exists an natural number $n1$ such that $0 < n1 < n$ and $b ^ {n1} = 1$.
Then, $g ^ {m * n1} = g ^ {m * n1 * (n * u + m * v)} = g ^ {m * n1 * n * u} * g ^ {m * n1 * m * v} = (g ^ {m n}) ^ {n1 * u} * ((g ^ {m * v}) ^ {n1}) ^ m = 1$. But $0 < m * n1 < m * n$, which yields a contradiction with the condition that $o(g) = m n$.

By construction, we know that $a, b$ are powers of $g$.
-/

theorem exercise_127 {G : Type u} [Group G] (g : G) (m n : ℕ) (mpos : m > 0) (npos : n > 0) (h_coprime : Nat.Coprime m n) (h_order_g : orderOf g = m * n) : ∃ (a b : G), (g = a * b) ∧ (orderOf a = m) ∧ (orderOf b = n) ∧ (∃ (u : ℤ), a = g ^ u) ∧ (∃ (v : ℤ), b = g ^ v) := by
  -- Since $gcd(m, n) = 1$, by Bezout's theorem, there exists $u, v \in \mathbb{Z}$, such that $n * u + m * v = 1$.
  set u := (m : ℤ).gcdB n with hu
  set v := (m : ℤ).gcdA n with hv
  have huv : n * u + m * v = 1 := by
    rw [hu, hv, add_comm, ← Int.gcd_eq_gcd_ab m n]
    have : (m : ℤ).gcd n = 1 := h_coprime
    rw [this, Nat.cast_one]
  -- Now take $a = g ^ {n u}, b = g ^ {m v}$.
  use g ^ (n * u), g ^ (m * v)
  constructor
  -- Then $g = a b$ holds trivially.
  · group
    rw [huv, zpow_one]
  · constructor
    -- To prove that $o(a) = m$, it suffices to show that $a ^ {m} = 1$ and that there is no other natural number $m1$ such that $0 < m1 < m$ and $a ^ {m1} = 1$.
    · apply (orderOf_eq_iff mpos).mpr
      constructor
      -- $a ^ {m} = 1$ holds trivially.
      · calc
        _ = (g ^ (m * n)) ^ u := by group
        _= _ := by rw [((orderOf_eq_iff (x := g) (n := m * n) (by positivity)).mp h_order_g).1]; simp only [one_zpow]
      -- Assume the contrary, that there exists an natural number $m1$ such that $0 < m1 < m$ and $a ^ {m1} = 1$.
      · rintro m1 m1lt m1pos poweq1
        -- Then, $g ^ {n * m1} = g ^ {n * m1 * (n * u + m * v)} = g ^ {n * m1 * n * u} * g ^ {n * m1 * m * v} = ((g ^ {n * u * m1}) ^ n * (g ^ {n * m}) ^ {m1 * v} = 1$.
        have : g ^ (n * m1) = 1 := by
          calc
          _ = g ^ (n * m1 * (n * u + m * v)) := by simp only [huv, mul_one, ← zpow_natCast, Nat.cast_mul]
          _ = g ^ (n * m1 * n * u) * g ^ (n * m1 * m * v) := by
            ring_nf
            rw[add_comm, zpow_add]
          _ = (g ^ (n * u * (m1 : ℤ))) ^ n * (g ^ (n * m)) ^ (m1 * v) := by
            congr 1;
            · have : n * m1 * n * u = (n * u * m1) * n := by ring
              simp only [this, zpow_mul, zpow_natCast]
            · have : n * m1 * m * v = ((n * m) : ℤ) * (m1 * v) := by ring
              simp only [this, zpow_mul, ← zpow_natCast, Nat.cast_mul]
          _ = 1 := by
            have : g ^ (n * u * (m1 : ℤ)) = (g ^ (n * u)) ^ m1 := by simp only[zpow_mul, zpow_natCast]
            rw [this, poweq1, mul_comm n m, ((orderOf_eq_iff (x := g) (n := m * n) (by positivity)).mp h_order_g).1, one_pow, one_zpow, one_mul]
        -- But $0 < n * m1 < m * n$, which yields a contradiction with the condition that $o(g) = m n$.
        absurd ((orderOf_eq_iff (x := g) (n := m * n) (by positivity)).mp h_order_g).2 (n * m1) (by rw[mul_comm m n]; apply mul_lt_mul_of_pos_left; assumption; assumption) (by positivity) this
        simp only [not_false_eq_true]
    · constructor
      -- To prove that $o(b) = n$, it suffices to show that $b ^ {n} = 1$ and that there is no other natural number $n1$ such that $0 < n1 < n$ and $b ^ {n1} = 1$.
      · apply (orderOf_eq_iff npos).mpr
        constructor
        -- $b ^ {n} = 1$ holds trivially.
        · calc
          _ = (g ^ (m * n)) ^ v := by group
          _ = _ := by rw [((orderOf_eq_iff (x := g) (n := m * n) (by positivity)).mp h_order_g).1];  simp only [one_zpow]
        -- Assume the contrary, that there exists an natural number $n1$ such that $0 < n1 < n$ and $b ^ {n1} = 1$.
        · rintro n1 n1lt n1pos poweq1
          -- Then, $g ^ {m * n1} = g ^ {m * n1 * (n * u + m * v)} = g ^ {m * n1 * n * u} * g ^ {m * n1 * m * v} = (g ^ {m n}) ^ {n1 * u} * ((g ^ {m * v}) ^ {n1}) ^ m = 1$.
          have : g ^ (m * n1) = 1 := by
            calc
            _ = g ^ (m * n1 * (n * u + m * v)) := by
              simp only [huv, mul_one, ← zpow_natCast, Nat.cast_mul]
            _ = g ^ (m * n1 * n * u) * g ^ (m * n1 * m * v) := by
              ring_nf
              rw [zpow_add]
            _ = (g ^ (m * n)) ^ (n1 * u) * ((g ^ (m * v)) ^ n1) ^ m := by
              congr 1;
              · have : m * n1 * n * u = (m * n) * (n1 * u) := by ring
                simp only [this, zpow_mul, ← zpow_natCast, Nat.cast_mul]
              · have : m * n1 * m * v = (m * v) * n1 * m := by ring
                simp only [this, zpow_mul, ← zpow_natCast]
            _ = 1 := by
              simp only [((orderOf_eq_iff (x := g) (n := m * n) (by positivity)).mp h_order_g).1, poweq1, one_zpow, one_pow, one_mul]
          -- But $0 < m * n1 < m * n$, which yields a contradiction with the condition that $o(g) = m n$.
          absurd ((orderOf_eq_iff (x := g) (n := m * n) (by positivity)).mp h_order_g).2 (m * n1) (by apply mul_lt_mul_of_pos_left; assumption; assumption) (by positivity) this
          simp only [not_false_eq_true]
      -- By construction, we know that $a, b$ are powers of $g$.
      · exact ⟨⟨n * u, by rfl⟩, ⟨m * v, by rfl⟩⟩

/-
185.
Suppose $G$ is a group, $A, B$ are two subgroups of $G$. Suppose $a, b \in G$ satisfy that $Aa = Bb$, Prove that $A = B$.

-/

theorem exercise_185 {G : Type u} [Group G] (A B : Subgroup G) (a b : G) (h : ({g * a| g ∈ A} : Set G) = ({g * b| g ∈ B} : Set G)) : A = B := by
  have h1A : 1 ∈ A := by exact Subgroup.one_mem A
  have h1B : 1 ∈ B := by exact Subgroup.one_mem B
  have hA : b * a⁻¹ ∈ A := by
    have : b ∈ {x | ∃ g ∈ A, g * a = x} := by
      rw [h]
      simp only [Set.mem_setOf_eq, mul_left_eq_self, exists_eq_right, h1B]
    rcases this with ⟨g1, g1A, hg1⟩
    have : g1 = b * a⁻¹ := by
      calc
      _ = (g1 * a) * a⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
      _ = _ := by rw [hg1]
    rw [this] at g1A
    exact g1A
  have hB : a * b⁻¹ ∈ B := by
    have : a ∈ {x | ∃ g ∈ B, g * b = x} := by
      rw [← h]
      simp only [Set.mem_setOf_eq, mul_left_eq_self, exists_eq_right, h1A]
    rcases this with ⟨g2, g2B, hg2⟩
    have : g2 = a * b⁻¹ := by
      calc
      _ = (g2 * b) * b⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
      _ = _ := by rw [hg2]
    rw [this] at g2B
    exact g2B
  ext x;
  constructor
  · intro xA
    have : x * (b * a⁻¹) ∈ A := by exact (Subgroup.mul_mem_cancel_right A hA).mpr xA
    have : (x * (b * a⁻¹)) * a ∈ {x | ∃ g ∈ B, g * b = x} := by
      rw [← h]
      use x * (b * a⁻¹)
    rcases this with ⟨g3, g3B, hg3⟩
    have : g3 = x := by
      calc
      _ = (g3 * b) * b⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
      _ = _ := by
        rw [hg3]
        group
    rw [this] at g3B
    exact g3B
  · intro xB
    have : x * (a * b⁻¹) ∈ B := by exact (Subgroup.mul_mem_cancel_right B hB).mpr xB
    have : (x * (a * b⁻¹)) * b ∈ {x | ∃ g ∈ A, g * a = x} := by
      rw [h]
      use x * (a * b⁻¹)
    rcases this with ⟨g4, g4A, hg4⟩
    have : g4 = x := by
      calc
      _ = (g4 * a) * a⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
      _ = _ := by
        rw [hg4]
        group
    rw [this] at g4A
    exact g4A

/-
342.
If $f : A \mapsto B, g : B \mapsto C$ are bijections, prove that $g f : A \mapsto C$ is also a bijection.

-/

instance exercise_342 {A B C : Type*} (f : A ≃ B) (g : B ≃ C) : A ≃ C where
  toFun := fun x ↦ g (f x)
  invFun := fun x ↦ f.invFun (g.invFun x)
  left_inv x := by simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply]
  right_inv x := by simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply]

/-
347.
Suppose $G$ is a Semigroup, if $\forall a, b \in G$, the equations $x a = b$ and $a y = b$ has solutions in $G$ then $G$ is a group.

-/

noncomputable instance exercise_347 {G : Type u} [Semigroup G] (u : G) (h : ∀ a b : G, (∃ x : G, x * a = b) ∧ (∃ y : G, a * y = b)) : Group G where
  mul := fun x y ↦ x * y
  mul_assoc x y z := mul_assoc x y z
  one := Classical.choose (h u u).1
  one_mul x := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry
