import Mathlib

open Set
open Subgroup
--10 : 设 $M$ 和 $N$ 分别是群 $G$ 的正规子群. 如果 $M \cap N=1$, 则对任意 $a \in M, b \in N$ 有 $a b=b a$.

-- First, we show that the commutator $a * b * a ^{-1} * b^{-1} \in H $.
-- Because $a ^ {-1} \in H$, we have $b * a ^{-1} * b^{-1} \in H$ since $H$ is normal. Thus $a * b * a ^{-1} * b^{-1} \in H.$
-- We also have $a * b * a ^{-1} * b^{-1} \in H'$.
-- This is because $a * b * a ^{-1} \in H'$ and $b \in H'$.
-- Thus $a * b * a ^{-1} * b^{-1} \in H \cap H' = 1$, so $a * b * a ^{-1} * b^{-1} = 1$.
-- Thus we get $a * b = b * a$.
theorem exercise10 {G : Type*} [Group G] {H H' : Subgroup G} [H.Normal] [H'.Normal] (h : H ⊓ H' = ⊥) (a b : G) (ha : a ∈ H) (hb : b ∈ H') : a * b = b * a := by
  -- First, we show that the commutator $a * b * a ^{-1} * b^{-1} \in H $.
  have in_H : a * b * a⁻¹ * b⁻¹ ∈ H := by
    -- Because $a ^ {-1} \in H$,
    have ha_inv: a⁻¹ ∈ H := H.inv_mem ha
    -- we have $b * a ^{-1} * b^{-1} \in H$ since $H$ is normal.
    have : b * a⁻¹ * b⁻¹ ∈ H := Subgroup.Normal.conj_mem (by assumption) a⁻¹ ha_inv b
    -- Thus $a * b * a ^{-1} * b^{-1} \in H.$
    have triv: a * (b * a⁻¹ * b⁻¹) ∈ H := mul_mem ha this
    have : a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by group
    rw[this] at triv
    exact triv
  -- We also have $a * b * a ^{-1} * b^{-1} \in H'$.
  have in_H' : a * b * a⁻¹ * b⁻¹ ∈ H' := by
    -- This is because $a * b * a ^{-1} \in H'$
    have : a * b * a⁻¹ ∈ H' := Subgroup.Normal.conj_mem (by assumption) b hb a
    -- and $b \in H'$.
    have hb_inv: b⁻¹ ∈ H' := H'.inv_mem hb
    exact mul_mem this hb_inv
  -- Thus $a * b * a ^{-1} * b^{-1} \in H \cap H' = 1$,
  have : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h]
    exact ⟨in_H, in_H'⟩
  -- so $a * b * a ^{-1} * b^{-1} = 1$.
  have eq_1 : a * b * a⁻¹ * b⁻¹ = 1:= this
  -- Thus we get $a * b = b * a$.
  have : a * b * a⁻¹ * b⁻¹ * b * a = b * a := by
    simp only [eq_1, one_mul]
  simp at this
  exact this

-- It suffices to show that $a * b * a⁻¹ * b⁻¹ = 1$
-- First, we show that the commutator $a * b * a ^{-1} * b^{-1} \in H $.
-- Because $a ^ {-1} \in H$, we have $b * a ^{-1} * b^{-1} \in H$ since $H$ is normal. Thus $a * b * a ^{-1} * b^{-1} \in H.$
-- We also have $a * b * a ^{-1} * b^{-1} \in H'$.
-- This is because $a * b * a ^{-1} \in H'$ and $b \in H'$.
-- Thus $a * b * a ^{-1} * b^{-1} \in H \cap H' = 1$, so $a * b * a ^{-1} * b^{-1} = 1$.
theorem exercise10' {G : Type*} [Group G] {H H' : Subgroup G} [H.Normal] [H'.Normal] (h : H ⊓ H' = ⊥) (a b : G) (ha : a ∈ H) (hb : b ∈ H') : a * b = b * a := by
  -- It is suffice to show that $a * b * a⁻¹ * b⁻¹ = 1$
  suffices h0 : a * b * a⁻¹ * b⁻¹ = 1 by
    have h0' : a * b * a⁻¹ * b⁻¹ * b * a = b * a := by simp only [h0, one_mul]
    simp at h0'
    exact h0'
  -- First, we show that the commutator $a * b * a ^{-1} * b^{-1} \in H $.
  have in_H : a * b * a⁻¹ * b⁻¹ ∈ H := by
    -- Because $a ^ {-1} \in H$,
    have ha_inv: a⁻¹ ∈ H := H.inv_mem ha
    -- we have $b * a ^{-1} * b^{-1} \in H$ since $H$ is normal.
    have : b * a⁻¹ * b⁻¹ ∈ H := Subgroup.Normal.conj_mem (by assumption) a⁻¹ ha_inv b
    -- Thus $a * b * a ^{-1} * b^{-1} \in H.$
    have triv: a * (b * a⁻¹ * b⁻¹) ∈ H := mul_mem ha this
    have : a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by group
    rw[this] at triv
    exact triv
  -- We also have $a * b * a ^{-1} * b^{-1} \in H'$.
  have in_H' : a * b * a⁻¹ * b⁻¹ ∈ H' := by
    -- This is because $a * b * a ^{-1} \in H'$
    have : a * b * a⁻¹ ∈ H' := Subgroup.Normal.conj_mem (by assumption) b hb a
    -- and $b \in H'$.
    have hb_inv: b⁻¹ ∈ H' := H'.inv_mem hb
    exact mul_mem this hb_inv
  -- Thus $a * b * a ^{-1} * b^{-1} \in H \cap H' = 1$,
  have : a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h]
    exact ⟨in_H, in_H'⟩
  -- Done
  exact this

/---14 : 设 $n$ 是正整数, 试证: 满足方程 $x^{n}=1$ 的复数的集合 $G$ 在通常乘法下是一个 $n$ 阶循环群.
def nthRootsOfUnity (n : ℕ) : Set ℂ := {x | x^n = 1}
#check IsCyclic

instance {n : ℕ} : Group (nthRootsOfUnity n) where
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  mul_left_inv := sorry


theorem exercise14 {n : ℕ} (h : 1 ≤ n): IsCyclic (nthRootsOfUnity n) ∧ Nat.card (nthRootsOfUnity n) = n  := by
  sorry

#check Complex-/

--theorem exercise14

--23 : 设 $A, B$ 分别是群 $G$ 的两个子群, 试证 $A \cup B$ 是 $G$ 的子群当且仅当 $A \leqslant B$ 或 $B \leqslant A$. 利用这个事实证明群 $G$ 不能表示成两个真子群的并.
--case1 : →
--Proof by contradiction
--Then $A \nsubeq B$ and $B \nsubeq A$
--Then there exist $x \in B x \nin A$  and  $y \in A y \nin B$
--Especially $x,y \in C$
--Then $x * y \in C$
--Then $x * y \in A$ or $x * y \in B$
--When $x * y \in A$ , $ x = (x *  y) * y ^{-1} \in A$ contradicts $x \nin A$
--When $x * y \in B$ , $ y = x ^{-1} * (x * y) \in B$ contradicts $y \nin B$
--We get an contradiction.
--case2 : ←
--When $A \subeq B$ , $B$ is what we seek
--When $B \subeq A$ , $A$ is what we seek,done
theorem exercise23_1 {G : Type*} [Group G] {A B : Subgroup G} : (∃ C : Subgroup G , C.carrier = (A.carrier ∪ B.carrier) ) ↔ (A.carrier ⊆ B.carrier) ∨ (B.carrier ⊆ A.carrier) := by
  constructor
  · intro hc
    --Proof by contradiction
    by_contra no_ss
    --Then $A \nsubeq B$ and $B \nsubeq A$
    have nssa : ¬ (A.carrier ⊆ B.carrier) := by tauto
    have nssb : ¬ (B.carrier ⊆ A.carrier) := by tauto
    --Then there exist $x \in B x \nin A$  and  $y \in A y \nin B$
    have BnA : ∃ x ∈ B.carrier , x ∉ A.carrier := by apply not_subset.mp nssb
    have AnB : ∃ y ∈ A.carrier , y ∉ B.carrier := by apply not_subset.mp nssa
    rcases BnA with ⟨x,hx1,hx2⟩
    rcases AnB with ⟨y,hy1,hy2⟩
    rcases hc with ⟨C,hc⟩
    --Especially $x,y \in C$
    have xc : x ∈ C := by
      show x ∈ C.carrier
      rw[hc]
      simp only [Set.mem_union,hx1, or_true]
    have yc : y ∈ C := by
      show y ∈ C.carrier
      rw[hc]
      simp only [Set.mem_union,hy1, true_or]
      --Then $x * y \in C$
    have xyc : x * y ∈ C := mul_mem xc yc
    have xyab' : x * y ∈ (A.carrier ∪ B.carrier) := by
      rw [← hc]
      exact xyc
    --Then $x * y \in A$ or $x * y \in B$
    have xyab : x * y ∈ A ∨ x * y ∈ B := xyab'
    rcases xyab with xya|xyb
    --When $x * y \in A$ , $ x = (x *  y) * y ^{-1} \in A$ contradicts $x \nin A$
    · have y_inv : y⁻¹ ∈ A := inv_mem hy1
      have : x * y * y⁻¹ ∈ A := mul_mem xya y_inv
      simp only [mul_inv_cancel_right] at this
      absurd this
      exact hx2
    --When $x * y \in B$ , $ y = x ^{-1} * (x * y) \in B$ contradicts $y \nin B$
    · have x_inv : x⁻¹ ∈ B := inv_mem hx1
      have : x⁻¹ * (x * y) ∈ B := mul_mem x_inv xyb
      simp only [inv_mul_cancel_left] at this
      absurd this
      exact hy2
  · intro hab
    rcases hab with ha|hb
    --When $A \subeq B$ , $B$ is what we seek
    · use B
      apply (Set.union_eq_right.mpr ha).symm
    --When $B \subeq A$ , $A$ is what we seek
    · use A
      apply (Set.union_eq_left.mpr hb).symm

theorem exercise23_2 {G : Type*} [Group G] {A B: Subgroup G} (Ap : A.carrier ≠ ⊤) (Bp : B.carrier ≠ ⊤) : (A.carrier ∪ B.carrier) ≠ ⊤ := by
  by_contra h
  have exist : ∃ C : Subgroup G , C.carrier = (A.carrier ∪ B.carrier) := by
    use ⊤
    rw[h]
    rfl
  have ss: (A.carrier ⊆ B.carrier) ∨ (B.carrier ⊆ A.carrier) := by
    apply exercise23_1.mp
    exact exist
  have : ((A.carrier ∪ B.carrier) = B.carrier) ∨ ((A.carrier ∪ B.carrier) = A.carrier) := by
    simp only [union_eq_left, union_eq_right,ss]
  rcases this with ha|hb
  · rw [ha] at h
    absurd Bp
    exact h
  · rw [hb] at h
    absurd Ap
    exact h

--24 ： 设 $\alpha$ 是群 $G$ 的一个自同构. 如果对任意 $g \in G, g^{-1} \\alpha(g) \in Z(G)$,则对导群 $G^{\prime}$ 的任意元 $a, \alpha(a)=a$.
--It is suffice to show $\all a b \in G , \alpha (a * b * a^{-1} * b^{-1}) = a * b * a^{-1} * b^{-1}$
--Which is eqivalent to $ b * a * b^{-1} * a^{-1} * \alpha (a) * \alpha (b) * \alpha (a^{-1}) * \alpha (b^{-1}) = 1$
--On the equation above,
--LHS $ = b * a * b^{-1} *  \alpha (b) * a^{-1} * \alpha (a) * \alpha (a^{-1}) * \alpha (b^{-1}) $
--$ = b * a * b^{-1} *  \alpha (b) * a^{-1} * \alpha (b^{-1}) $
--$ = b * b^{-1} *  \alpha (b) * a * a^{-1} * \alpha (b^{-1}) $
--$ = \alpha (b) * \alpha (b^{-1}) = 1$
theorem exercise24 {G : Type*} [Group G] (α : G ≃* G) (h : ∀ g : G, g⁻¹ * ( α g ) ∈ Subgroup.center G ) (a b : G) : α (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by
  --It is suffice to show $\all a b \in G , \alpha (a * b * a^{-1} * b^{-1}) = a * b * a^{-1} * b^{-1}$
  simp only [map_mul]
  --Which is eqivalent to $ b * a * b^{-1} * a^{-1} * \alpha (a) * \alpha (b) * \alpha (a^{-1}) * \alpha (b^{-1}) = 1$
  suffices h0 : b * a * b⁻¹ * a⁻¹ * (α a) * (α b) * (α a⁻¹) * (α b⁻¹) = 1 by
    have h1 : a * b * a⁻¹ * b⁻¹ * (b * a * b⁻¹ * a⁻¹ * (α a) * (α b) * (α a⁻¹) * (α b⁻¹)) = a * b * a⁻¹ * b⁻¹ := by
      rw[h0]
      simp only [mul_one]
    have h2 : a * b * a⁻¹ * b⁻¹ * (b * a * b⁻¹ * a⁻¹ * (α a) * (α b) * (α a⁻¹) * (α b⁻¹)) = (α a) * (α b) * (α a⁻¹) * (α b⁻¹) := by group
    rw[h2] at h1
    exact h1
  have H : ∀ g x : G, x * ( g⁻¹ * ( α g )) = (g⁻¹ * ( α g ) ) * x := by
    intro g
    apply Subgroup.mem_center_iff.mp (h g)
  have h3 : b * a * b⁻¹ * a⁻¹ * (α a) * (α b) * (α a⁻¹) * (α b⁻¹) = 1 := by
    calc
      --LHS $ = b * a * b^{-1} *  \alpha (b) * a^{-1} * \alpha (a) * \alpha (a^{-1}) * \alpha (b^{-1}) $
      _= b * a * b⁻¹ * ((a⁻¹ * (α a)) * (α b) ) * (α a⁻¹) * (α b⁻¹) := by
        group
      _= b * a * b⁻¹ * ( (α b) * (a⁻¹ * (α a)) ) * (α a⁻¹) * (α b⁻¹) := by
        rw [(H a (α b)).symm]
      _= b * a * b⁻¹ * (α b) * a⁻¹ * ((α a) * (α a⁻¹)) * (α b⁻¹) := by
        group
      --$ = b * a * b^{-1} *  \alpha (b) * a^{-1} * \alpha (b^{-1}) $
      _= b * a * b⁻¹ * (α b) * a⁻¹ * (α b⁻¹) := by
        simp only [map_inv, mul_right_inv, mul_one]
      _= b * ( a * ( b⁻¹ * (α b) ) ) * a⁻¹ * (α b⁻¹) := by
        group
      --$ = b * b^{-1} *  \alpha (b) * a * a^{-1} * \alpha (b^{-1}) $
      _= b * ( ( b⁻¹ * (α b) ) * a ) * a⁻¹ * (α b⁻¹) := by
        rw[(H b a)]
      --$ = \alpha (b) * \alpha (b^{-1}) = 1$
      _= b * b⁻¹ * (α b) * (α b⁻¹) := by
        group
      _=_ := by
        simp only [mul_right_inv, one_mul, map_inv]
  exact h3

--37 : 群 $G$ 没有非平凡子群的充分必要条件是 $G=\\{1\\}$ 或是素数阶循环群
--Prove by contradiction
--$ G \ne {1} $ exist $g0 \in G, g0 \ne 1$
--then any $g \ne 1 $, then $\< g \> = G $ because $\< g \> \ne 1$
--If $order of g0 = 0 $ $ 1 \ne g0 * g0 $
--Then $\< g0 * g0 \> = G $ thus contain $g0$
--We have some $k$ ,$ (g0 * g0) ^ k = g0$ so $ g0 ^ (2 * k -1) = 1$
--This contradicts with order zero
--If $order of g0 > 0$ and $ |G| $ is not a prime
--Any $ g \ne 1 $, then $\< g \> = G $ so $ order of g = |G| $ is all the same
--$order of g0 = |G|$ thus not a prime and fnite,exist $1 < a < order of g0, a | order of g0 $
--Especially $ 1 \ne g0 ^ a $ because $a < |G| = order of g0$
--But $(g0 ^ a)^(order of g0/a) = 1$ the order isn't equal to $|G|$ contradicts



theorem exercise37 {G : Type*} [Group G] (h : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) : Nat.card G = 1 ∨ (IsCyclic G ∧ (Nat.card G).Prime) := by
  --Prove by contradiction
  by_contra
  --$ G \ne {1} $ exist $g \in G, g \ne 1$
  have ntriv : ¬ Nat.card G = 1 := by tauto
  have ne1 : ∃ g₀ : G, g₀ ≠ 1 := by
    by_contra all1
    absurd ntriv
    push_neg at all1
    haveI : Unique G := {
      default := 1
      uniq := all1 }
    apply Nat.card_unique
  have ncardp : ¬ (IsCyclic G ∧ (Nat.card G).Prime) := by tauto
  rcases ne1 with ⟨g₀,hg₀⟩
  --then any $g \ne 1 $, then $\< g \> = G $ because $\< g \> \ne 1$
  have eqtop : ∀ g : G , g ≠ 1 → ↑(zpowers g) = ⊤ := by
    intro g hg
    have gptriv : ↑(zpowers g) = ⊥ ∨ ↑(zpowers g) = ⊤ := h ↑(zpowers g)
    by_contra netop
    simp only [zpowers_eq_bot, netop, or_false] at gptriv
    absurd gptriv
    exact hg
  have eqtop0 : ↑(zpowers g₀) = ⊤ := eqtop g₀ hg₀
  have cyc : IsCyclic G := ⟨by
    show ∃ g : G, ∀ x, x ∈ zpowers g
    use g₀
    simp only [eqtop0,mem_top, forall_const]⟩
  simp only [cyc, true_and] at ncardp
  by_cases ord0 : orderOf g₀ = 0
  --If $order of g0 = 0 $ $ 1 \ne g0 * g0 $
  · have : g₀ * g₀ ≠ 1 := by
      rw [ Eq.symm (pow_two g₀) ]
      apply orderOf_eq_zero_iff'.mp ord0 2
      norm_num
    --Then $\< g0 * g0 \> = G $ thus contain $g0$
    have eqtop':  ↑(zpowers (g₀ * g₀)) = ⊤ := eqtop (g₀ * g₀) this
    have : g₀ ∈ (zpowers (g₀ * g₀)) := by simp only [eqtop',mem_top]
    --We have some $k$ ,$ (g0 * g0) ^ k = g0$
    have existk : ∃ k : ℤ , (g₀ * g₀) ^ k = g₀ := by apply Subgroup.mem_zpowers_iff.mp this
    rcases existk with ⟨k,hk⟩
    --so $ g0 ^ (2 * k -1) = 1$
    have : (g₀ * g₀) ^ k = g₀ ^ (2 * k) := by
      calc
      _ = (g₀^2) ^ k := by congr; exact Eq.symm (zpow_two g₀)
      _ = _ := (zpow_mul _ _ _).symm
    rw[this] at hk
    have : g₀ ^ (2 * k - 1) = 1 := by
      calc
      _= g₀ ^ (2 * k - 1) * g₀ * g₀⁻¹ := by group
      _= g₀ ^ (2 * k) * g₀⁻¹ := by simp only [mul_zpow_self g₀ (2 * k - 1), sub_add_cancel]
      _=_ := by simp only [hk, mul_right_inv]
    --This contradicts with order zero
    absurd this
    have : 2 * k - 1 ≠ 0 := by omega
    apply orderOf_eq_zero_iff.mp at ord0
    apply isOfFinOrder_iff_zpow_eq_one.mpr.mt at ord0
    push_neg at ord0
    exact ord0 (2 * k -1) this
  --If $order of g0 > 0$ and $ |G| $ is not a prime
  · have ordFin : 0 < orderOf g₀ := Nat.pos_iff_ne_zero.mpr ord0
    --Any $ g \ne 1 $, then $\< g \> = G $ so $ order of g = |G| $ is all the same
    have : ∀ g : G , g ≠ 1 → orderOf g = Nat.card G := by
      intro g hg
      have :∀ x, x ∈ zpowers g := by simp only [eqtop g hg,mem_top, forall_const]
      rw [← Nat.card_zpowers g, (eq_top_iff' (zpowers g)).mpr this]
      exact Nat.card_congr (Equiv.Set.univ _)
    have ntriv' : Nat.card G ≥ 2 := by
      apply (Nat.two_le_iff (Nat.card G)).mpr
      simp only [ne_eq, ntriv, not_false_eq_true, and_true]
      simp only [← this g₀ hg₀, ord0, not_false_eq_true]
    rw[← this g₀ hg₀] at ncardp
    rw[← this g₀ hg₀] at ntriv'
    --$order of g0 = |G|$ thus not a prime and fnite,exist $1 < a < order of g0, a | order of g0 $
    have np : ∃ m, m ∣ (orderOf g₀) ∧ 2 ≤ m ∧ m < (orderOf g₀) := Nat.exists_dvd_of_not_prime2 ntriv' ncardp
    rcases np with ⟨m,hm,ge2,ltord⟩
    --Especially $ 1 \ne g0 ^ a $ because $a < |G| = order of g0$
    have mne0 : m ≠ 0 := by linarith
    have ne1 : g₀ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf' mne0 ltord
    --But $(g0 ^ a)^(order of g0/a) = 1$ the order isn't equal to $|G|$ contradicts
    have ordne: orderOf (g₀ ^ m) = (orderOf g₀) / m := orderOf_pow_of_dvd mne0 hm
    rw[this (g₀ ^ m) ne1, ← this g₀ hg₀] at ordne
    absurd ordne
    apply Nat.ne_of_gt
    exact Nat.div_lt_self ordFin ge2

--191 : 设 $A$ 是群 $G$ 的非空有限子集, 则 $A$ 是 $G$ 的子群当且仅当对任意元 $a$, $b \\in A, a b \\in A$.

--lemma1 : $\all x \in A,\all n \in \mathbb {N} n > 0$ we have $ x^n \in A$
--by induction,for $n=1$ we have $x^1 \in A$
--when $x^n \in A$, we also have $x \in A$
--thus $x^(n+1) = x^n * x \in A$ done.

--lemma2 : $\all x \in A$ $x$ has finite order.
--prove by contradiction
--$x$ have infinite order, so $x^n \ne x^m$ for $n \ne m$
--but $n \mapsto x^n$ is not injective from $\mathbb {N} to A$ because $A$ is finite,contradicts


--lemma3 : $\all x \in A$ $x^{-1} \in A$
--if $x=1$ $x^{-1} = 1 \in A$
--else we have $x \ne 1$ thus $orderOf x \ge 2$
--by lemma1 $x^(orderOf x -1)$ is in A
--$x^(orderOf x -1) * x = x^(orderOf x) = 1$,thus $x^{-1} = x^(orderOf x -1) \in A$

--To prove the main theorem
--case1 : ←
--we only have to check that A is closed under multiplication,inversion and $1 \in A$
--closed under multiplication is given
--closed under inversion is proved by lemma3
--because A is nonempty there exist $x \in A$
--by closed under inversion is proved by lemma3
--$x^{-1} \in A$ thus $1 = x^{-1} * x \in A$
--case2 : →
--A is subgroup thus closed under multiplication

--lemma1 : $\all x \in A,\all n \in \mathbb {N} n > 0$ we have $ x^n \in A$
lemma exercise191_lemma1 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A) (x : G): x ∈ A → ∀ n, x ^ (n + 1) ∈ A := by
  intro xinA n
  --by induction,
  induction' n with n ih
  --for $n=1$ we have $x^1 \in A$
  · simp only [zero_add, pow_one,xinA]
  --when $x^n \in A$, we also have $x \in A$
  --thus $x^(n+1) = x^n * x \in A$ done.
  · rw[pow_succ x (n + 1)]
    apply h
    simp only [ih, xinA, and_self]

--lemma2 : $\all x \in A$ $x$ has finite order.
lemma exercise191_lemma2 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A) : ∀ x : G, x ∈ A → IsOfFinOrder x := by
  intro x xinA
  --prove by contradiction
  by_contra nfin
  have ord0: orderOf x = 0 := by apply orderOf_eq_zero_iff.mpr nfin
  --$x$ have infinite order, so $x^n \ne x^m$ for $n \ne m$
  have inj : ∀ n m : ℕ, x ^ n = x ^ m ↔ n = m := by
    intro n m
    apply pow_inj_iff_of_orderOf_eq_zero ord0
  absurd inj
  --but $n \mapsto x^n$ is not injective from $\mathbb {N} to A$ because $A$ is finite,contradicts
  have := Finite.exists_ne_map_eq_of_infinite (fun n ↦ (⟨x ^ (n + 1), exercise191_lemma1 A h x xinA n⟩ : A))
  simp only [ne_eq, Subtype.mk.injEq] at this
  rcases this with ⟨n,m,heq⟩
  push_neg
  use (n + 1),(m + 1)
  simp only [heq, ne_eq, add_left_inj, not_false_eq_true, and_self, not_true_eq_false, or_false]

--lemma3 : $\all x \in A$ $x^{-1} \in A$
lemma exercise191_lemma3 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A): ∀ x : G, x ∈ A → x⁻¹ ∈ A := by
  intro x xinA
  have : IsOfFinOrder x := exercise191_lemma2 A h x xinA
  by_cases eq1 : x = 1
  --if $x=1$ $x^{-1} = 1 \in A$
  · simp only [eq1, inv_one]
    rw [eq1] at xinA
    exact xinA
  --else we have $x \ne 1$ thus $orderOf x \ge 2$
  · have ordpos: orderOf x > 0 := IsOfFinOrder.orderOf_pos this
    have ordne1: orderOf x ≠ 1 := (orderOf_eq_one_iff.mp).mt eq1
    have ordge2: 2 ≤ orderOf x := by
      apply (Nat.two_le_iff (orderOf x)).mpr
      simp only [ne_eq, ordne1, not_false_eq_true, and_true,Nat.not_eq_zero_of_lt ordpos]
    --by lemma1 $x^(orderOf x -1)$ is in A
    have inv_inA': x ^ (orderOf x -2 + 1) ∈ A := exercise191_lemma1 A h x xinA (orderOf x - 2)
    --$x^(orderOf x -1) * x = x^(orderOf x) = 1$,thus $x^{-1} = x^(orderOf x -1) \in A$
    have : x ^ (orderOf x -2 + 1) = x⁻¹ := by
      calc
        _= x ^ (orderOf x -2 + 1) * x * x⁻¹ := by group
        _= x ^ (orderOf x -2 + 1 + 1) * x⁻¹ := by rw [pow_succ x (orderOf x -2 + 1)]
        _= x ^ (orderOf x -2 + 1 + 1) * x⁻¹ := by dsimp
        _= x ^ orderOf x * x⁻¹ := by rw [Nat.sub_add_cancel ordge2]
        _=_ := by simp only [pow_orderOf_eq_one x, one_mul]
    rw[← this]
    exact inv_inA'
--To prove the main theorem
--case1 : ←
def exercise191_1 {G : Type*} [Group G] (A : Finset G) (h : ∀ a b : G,a ∈ A ∧ b ∈ A → a * b ∈ A) (ne : A.Nonempty): Subgroup G where
  carrier := A
  --we only have to check that A is closed under multiplication,inversion and $1 \in A$
  --closed under multiplication is given
  mul_mem' := by
    intro a b ha hb
    apply h
    constructor
    · exact ha
    · exact hb
  --closed under inversion is proved by lemma3
  inv_mem' := by
    simp only [Finset.mem_coe]
    intro x
    exact exercise191_lemma3 A h x
  --because A is nonempty there exist $x \in A$
  one_mem' := by
    simp only [Finset.mem_coe]
    rcases ne with ⟨x,xinA⟩
    --by closed under inversion is proved by lemma3 $x^{-1} \in A$ thus $1 = x^{-1} * x \in A$
    have inv_inA: x⁻¹ ∈ A := exercise191_lemma3 A h x xinA
    rw [← mul_inv_self x]
    apply h
    simp [xinA,inv_inA]

--case2 : →
theorem exercise191_2 {G : Type*} [Group G] (A : Subgroup G) [Finite A] : ∀ a b : G, a ∈ A ∧ b ∈ A → a * b ∈ A := by
  --A is subgroup thus closed under multiplication
  intro a b hab
  apply mul_mem hab.1 hab.2

--70 : 设 $F$ 是有限域, $a, b \\in F^{*}$. 求证: 对每个 $c \\in F$, 方程 $a x^{2}+b y^{2}=c$在域 $F$ 中均有解 $(x, y)$.\n特别地, 有限域的任意元均可写成两个元的平方和.

#check Finset.card_le_mul_card_image_of_maps_to

theorem exercise70 {F : Type*} [Field F] [Fintype F] (a b : F) (ane0 : a ≠ 0) (bne0 : b ≠ 0): ∀ c : F, ∃ x y : F, a * x^2 + b * y^2 = c := by
  intro c
  let QR : Set F := {r | ∃ z : F, r = z^2}
  let S : Set F := {X | ∃ r : F, r ∈ QR ∧ X = a * r }
  let T : Set F := {Y | ∃ r : F, r ∈ QR ∧ Y = c - b * r }
  haveI : Fintype S := by exact Fintype.ofFinite ↑S
  haveI : Fintype T := by exact Fintype.ofFinite ↑T
  haveI : Fintype ((S ∪ T) : Set F) := by exact Fintype.ofFinite ↑(S ∪ T)
  haveI : Fintype QR := by exact Fintype.ofFinite ↑QR
  have Scard: Fintype.card S ≥ Fintype.card QR := by sorry
  have Tcard: Fintype.card T ≥ Fintype.card QR := by sorry
  have : 2 * Fintype.card QR ≥ Fintype.card F +1 := by sorry
  have : (S ∩ T).Nonempty := by
    by_contra H
    have : S ∩ T = ∅  := by exact not_nonempty_iff_eq_empty.mp H
    haveI : Disjoint S T := by exact disjoint_iff_inter_eq_empty.mpr this
    have sum: Fintype.card ((S ∪ T) : Set F) = Fintype.card S + Fintype.card T := by

      --apply Finset.card_union_of_disjoint
      sorry
    have : Fintype.card ((S ∪ T) : Set F) ≤ Fintype.card F := set_fintype_card_le_univ (S ∪ T)
    rw [sum] at this
    absurd this
    simp only [not_le]
    calc
     _< 2 * Fintype.card QR := by linarith
     _= Fintype.card QR + Fintype.card QR := by ring
     _≤_ := by linarith
  rcases this with ⟨l,hl⟩
  have : l ∈ S := by exact mem_of_mem_inter_left hl
  have : ∃ r : F, r ∈ QR ∧ l = a * r  := by exact this
  rcases this with ⟨rx,hrx⟩
  have : l ∈ T := by exact mem_of_mem_inter_right hl
  have : ∃ r : F, r ∈ QR ∧ l = c - b * r  := by exact this
  rcases this with ⟨ry,hry⟩
  have : ∃ x : F, rx = x^2 := by exact hrx.1
  rcases this with ⟨x,hx⟩
  have : ∃ y : F, ry = y^2 := by exact hry.1
  rcases this with ⟨y,hy⟩
  use x,y
  simp only [← hx, ← hrx.2, hry.2, ← hy, sub_add_cancel]
