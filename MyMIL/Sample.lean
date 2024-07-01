import Mathlib

/-!
This is the sample file of formalizing abstract algebra exercises.
-/

section

-- ID: 392 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote)

/-- `1` is the generator of ℤ⧸nℤ since for every $m$ in ℤ⧸nℤ, $m % n = m • (1 % n)$. -/
example (n : ℕ) : IsAddCyclic (ZMod n) where
  exists_generator := by
    use 1
    match n with
      | 0 => exact fun m ↦ ⟨m, mul_one m⟩
      | n + 1 =>
        intro ⟨m, h⟩
        use m
        show m • 1 = (⟨m, h⟩ : Fin (n + 1))
        induction m with
          | zero =>
            simp only [zero_smul, Fin.zero_eta]
          | succ m hm =>
            show m • 1 + 1 = (⟨m + 1, h⟩ : Fin (n + 1))
            simp only [hm (Nat.lt_trans (lt_add_one m) h), Fin.add_def, Fin.val_one',
              Nat.add_mod_mod, Fin.mk.injEq, Nat.mod_succ_eq_iff_lt.mpr h]

/-- The relation of `1` is $n • 1 = 0$ since $(n • 1) % n = n % n = 0 $. -/
example (n : ℕ) : n • 1 = (0 : ZMod n) := by
  match n with
    | 0 => simp only [zero_smul]
    | n + 1 => simp only [nsmul_eq_mul, CharP.cast_eq_zero, mul_one]

end



section

-- ID: 415 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote)

open DihedralGroup

/-- $\left(x \in D_{2 n} \mid x^{2}=1\right\}$ is not a subgroup of $D_{2 n}$ (here $n \geq 3$ ). -/
example {n : ℕ} (hn : 3 ≤ n) : ¬ ∃ H : Subgroup (DihedralGroup n), ∀ {x : DihedralGroup n}, x ∈ H ↔ x ^ 2 = 1 := by
  -- To the contrary, assuming that $\left\lbrace x \in D_{2 n} |\ x^{2}=1 \right\rbrace  $ is a subgroup $H$ of $D_{2 n}$.
  by_contra h
  rcases h with ⟨H, hH⟩
  -- $sr_0 ∈ H$ since the order of $sr_0$ is 2.
  have h0 : sr 0 ∈ H := hH.mpr ((orderOf_eq_iff (by norm_num)).mp (orderOf_sr _)).1
  -- $sr_1 ∈ H$ since the order of $sr_1$ is 2.
  have h1 : sr 1 ∈ H := hH.mpr ((orderOf_eq_iff (by norm_num)).mp (orderOf_sr _)).1
  -- $r ∈ H$ since $r = sr_0 * sr_1$. As a result, $r^2 = 1$.
  have hr : r (1 : ZMod n) ^ 2 = 1 := by
    apply hH.mp
    have hsr : sr (0 : ZMod n) * sr 1 = r 1 := by rw [sr_mul_sr, sub_zero]
    rw [← hsr]
    exact H.mul_mem h0 h1
  -- $r^2 ≠ 1$ since the order of $r$ is $n > 2$, which is a contradiction.
  exact ((orderOf_eq_iff (by linarith)).mp orderOf_r_one).2 2 (by linarith) (by norm_num) hr

end



section

-- ID: 418 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote)

open Subgroup MonoidHom

/-- If $K$ is cyclic, then $\mathrm{Aut}(K)$ is an abelian group. -/
instance {K : Type*} [Group K] [IsCyclic K] : CommGroup (MulAut K) := by
  -- In fact, only need to show that for all $f, g \in \mathrm{Aut}(K)$, $x \in K$, $f(g(x)) = g(f(x))$.
  apply CommGroup.mk
  intro f g
  ext x
  show f (g x) = g (f x)
  -- Since $K$ is cyclic, there exsits $m, n \in \mathbb{Z}$ such that $f(x) = x^m$ and $g(x) = x^n$.
  rcases map_cyclic f.toMonoidHom with ⟨m, hm⟩
  rcases map_cyclic g.toMonoidHom with ⟨n, hn⟩
  have hfg : f (g x) = (g x) ^ m := hm (g x)
  have hg : g x = x ^ n := hn x
  have hgf : g (f x) = (f x) ^ n := hn (f x)
  have hf : f x = x ^ m := hm x
  -- Substituting $f(x) = x^m$ and $g(x) = x^n$, we get $f(g(x)) = (x^n)^m = x^{mn} = (x^n)^m = g(f(x))$.
  rw [hfg, hg, hgf, hf, ← zpow_mul, ← zpow_mul, mul_comm]

/-- If $K$ is a normal subgroup of $G$ and $K$ is cyclic, then $G^{\prime} \le C_{G}(K)$. -/
example {G : Type*} [Group G] (K : Subgroup G) [IsCyclic K] [Normal K] : commutator G ≤ centralizer K := by
  -- $\le C_{G}(K)$ is the kernel of the homomorphism from $G$ to $\mathrm{Aut}(K)$ given by conjugation.
  have h : centralizer K = (@MulAut.conjNormal G _ K _).ker := by
    -- In fact, only need to show that for all $g \in G$, $g$ in $\le C_{G}(K)$ if and only if its conjugation action on $K$ is trival.
    ext g
    refine' Iff.trans _ MulEquiv.ext_iff.symm
    constructor
    -- On one hand, if $g$ in $\le C_{G}(K)$, then for all $x \in K$, $g * x = x * g$. As a result, $g * x * g⁻¹ = x$.
    · intro h x
      exact Subtype.val_inj.mp (eq_mul_inv_of_mul_eq (h x.val x.property)).symm
    -- On the other hand, if $g$ acts on $K$ trivally, then for all $x \in K$, $g * x * g⁻¹ = x$. As a result, $g * x = x * g$.
    · intro h x hx
      exact mul_eq_of_eq_mul_inv (Subtype.val_inj.mpr (h ⟨x, hx⟩)).symm
  -- Therefore, only need to show $G^{\prime}$ is in the kernel of the conjugation homomorphism.
  rw [h]
  -- Since $\mathrm{Aut}(K)$ is an abelian group, the kernel of any homomorphism from $G$ maps to it is in $C_{G}(K)$. As a result, $G^{\prime}$ is in the kernel of the conjugation homomorphism.
  exact Abelianization.commutator_subset_ker (@MulAut.conjNormal G _ K _)

end



-- ID: 428 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote)

namespace MvPolynomial

/--  Let $I$ be an index set and $S$ is a commutative semiring. Let $R = S[x_i, i \in I]$ be the set of polynomials with coefficients in $S$ of the independent variables $x_i, i \in I$. For each $\sigma \in S_I$ define a map $$ \sigma: R \rightarrow R \quad \text { by } \quad x_i \mapsto x_{\sigma(i)}, i \in I. $$ Prove that this defines a (left) group action of $S_I$ on $R$. -/
noncomputable instance perm_instMulAction (I : Type*) (S : Type*) [CommSemiring S] : MulAction (Equiv.Perm I) (MvPolynomial I S) where
  smul σ := eval₂ C (fun i ↦ X (σ i))
  one_smul p := by
    show eval₂Hom C (fun i↦ X ((1 : Equiv.Perm I) i)) p = RingHom.id (MvPolynomial I S) p
    -- $1 \in \mathrm{Aut}(I)$ acts trivially on each $x_i$, hence $1$ acts trivially on $S[x_i, i \in I]$.
    exact hom_congr_vars (RingHom.ext fun x ↦ bind₂_C_right C x)
      (fun i _ _ ↦ bind₁_X_right (fun i ↦ X i) i) (Eq.refl p)
  mul_smul σ τ p := by
    show eval₂Hom C (fun i ↦ X ((σ * τ) i)) p =
      (eval₂Hom C (fun i ↦ X (σ i))).comp (eval₂Hom C (fun i ↦ X (τ i))) p
    -- $\sigma * \tau $ maps $ x_i $ to $ x_{(\sigma(\tau(i)))},$, $\tau \text{ maps } x_i \text{ to } x_{\tau(i)}$, $\sigma \text{ maps } x_{(\tau i)} \text{ to } x_{(\sigma(\tau(i)))}$, thus $\sigma * \tau$ and $\sigma \circ \tau$ act the same on $S[x_i, i \in I]$.
    apply hom_congr_vars
    · apply RingHom.ext
      intro x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, eval₂Hom_C_eq_bind₁, RingHom.coe_comp,
        RingHom.coe_coe, algHom_C]
    · intro i _ _
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, eval₂Hom_C_eq_bind₁, RingHom.coe_coe,
        bind₁_X_right, RingHom.coe_comp]
    · rfl

/-- Let $n$ be a positive integer and let $R$ be the set of all polynomials withinteger coefficients in the independent variables $x_{1}, x_{2}, \ldots, x_{n}$, i.e., the members of $R$ are finite sums of elements of the form $a x_{1}^{r_{1}} x_{2}^{r_{2}} \cdots x_{n}^{r_{n}}$, where $a$ is any integer and $r_{1}, \ldots, r_{n}$ are nonnegative integers. For each $\sigma \in S_{n}$ define a map $$ \sigma: R \rightarrow R \quad \text { by } \quad \sigma \cdot p\left(x_{1}, x_{2}, \ldots, x_{n}\right)=p\left(x_{\sigma(1)}, x_{\sigma(2)}, \ldots, x_{\sigma(n)}\right) .$$ Prove that this defines a (left) group action of $S_{n}$ on $R$. -/
noncomputable example {n : ℕ} : MulAction (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) ℤ) :=
  perm_instMulAction (Fin n) ℤ

end MvPolynomial



section

-- ID: 1037 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote) 82

open Interval

/-- Let $X$ be a subset of $\mathbb{R}$, $a b \in X$, $R = C(X, \mathbb{R})$ be the ring of all continuous functions on $X$, then $I = \{f \in R | f(a) = f(b) = 0\}$ is an ideal of $R$. -/
def eq_zero_at_two_pt {X : Set ℝ} (a b : X) : Ideal C(X, ℝ) where
  carrier := { f | f a = 0 ∧ f b = 0 }
  -- If $f, g \in I$, then $f(a) = f(b) = g(a) = g(b) = 0$, so $(f + g)(a) = f(a) + g(a) = 0$ and $(f + g)(b) = f(b) + g(b) = 0$.
  add_mem' hf hg := ⟨Linarith.eq_of_eq_of_eq hf.1 hg.1, Linarith.eq_of_eq_of_eq hf.2 hg.2⟩
  zero_mem' := ⟨rfl, rfl⟩
  -- If $f \in R$ and $g \in I$, then $g(a) = g(b) = 0$, so $(fg)(a) = f(a)g(a) = 0$ and $(fg)(b) = f(b)g(b) = 0$.
  smul_mem' _ _ hg := ⟨mul_eq_zero_of_right _ hg.1, mul_eq_zero_of_right _ hg.2⟩

/-- Let $X$ be a subset of $\mathbb{R}$, $a b \in X$, $R = C(X, \mathbb{R})$ be the ring of all continuous functions on $X$, then $I = \{f \in R | f(a) = f(b) = 0\}$ is an ideal of $R$. -/
theorem eq_zero_at_two_pt_not_isPrime {X : Set ℝ} {a b : X} (h : a.1 ≠ b.1) : ¬ (eq_zero_at_two_pt a b).IsPrime := by
  -- To the contrary, assuming that $I$ is a prime ideal of $R$.
  intro hp
  let f : C(X, ℝ) := {
    -- Let $f(x) = x - a$.
    toFun := fun x ↦ x - a
    -- Then $f \in R$ since the diffence of two continuous functions is continuous.
    continuous_toFun := Continuous.sub continuous_subtype_val continuous_const
  }
  let g : C(X, ℝ) := {
    -- Let $g(x) = x - b$.
    toFun := fun x ↦ x - b
    -- Then $g \in R$ since the diffence of two continuous functions is continuous.
    continuous_toFun := Continuous.sub continuous_subtype_val continuous_const
  }
  -- Since $f(a) = g(b) = 0$, $ f(a) * g(a) = f(b) * g(b) = 0$. As a result, $f * g \in I$.
  have hfg : f * g ∈ eq_zero_at_two_pt a b := ⟨
    mul_eq_zero_of_left (sub_self a.1) (g a),
    mul_eq_zero_of_right (f b) (sub_self b.1)⟩
  -- But $f, g \notin I$ since $f(b) = b - a \ne 0$ and $g(a) = a - b \ne 0$, which contradicts the assumption that $I$ is a prime ideal.
  exact not_or.mpr ⟨not_and.mpr fun _ ↦ sub_ne_zero_of_ne h.symm,
    not_and.mpr fun a _ ↦ sub_ne_zero_of_ne h a⟩ (hp.2 hfg)

/-- Let $R$ be the ring of all continuous functions on $[0, 1]$ and let $I$ be the collection of functions $f(x)$ in $R$ with $f(1 / 3)=f(1 / 2)=0$. Then $I$ is an ideal of $R$. -/
noncomputable def eq_zero_at_one_div_three_and_one_div_two : Ideal C([[(0 : ℝ), 1]], ℝ) :=
  eq_zero_at_two_pt ⟨1 / 3, ⟨by norm_num, by norm_num⟩⟩ ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩

/-- $I$ is not a prime ideal of $R$. -/
noncomputable example : ¬ eq_zero_at_one_div_three_and_one_div_two.IsPrime :=
  eq_zero_at_two_pt_not_isPrime (by
    intro h
    dsimp at h
    linarith
)

end



-- ID: 1048 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote) 87

namespace Subgroup

/-- Let $H$ be a subgroup of order $2$ in $G$. Then $N_{G}(H)=C_{G}(H)$. -/
theorem normalizer_eq_centralizer_of_card_eq_two {G : Type*} [Group G] [DecidableEq G] {H : Subgroup G} [Fintype H] (hH : Fintype.card H = 2) : H.normalizer = centralizer H := by
  apply le_antisymm
  -- First we show that $N_{G}(H) \le C_{G}(H)$. In fact, let $g \in N_{G}(H)$ and $x \in H$.
  · intro g hg x hx
    by_cases h : x = 1
    -- If $x = 1$ then $g * x = g = x * g$.
    · simp only [h, one_mul, mul_one]
    -- Otherwise $x \ne 1$, then $g * x * g^{-1} \ne 1$.
    · have hgx : g * x * g⁻¹ ≠ 1 := fun hxg ↦ h (conj_eq_one_iff.mp hxg)
      -- Let $S = H \setminus \{1\}$.
      let S : Finset G := H.carrier.toFinset.erase 1
      -- Then $x \in S$ since $x \in H$ and $x \ne 1$.
      have hxs : x ∈ S := Finset.mem_erase_of_ne_of_mem h (Set.mem_toFinset.mpr hx)
      -- Moreover, $g * x * g^{-1} \in H$ since $g \in N_{G}(H)$. But $g * x * g^{-1} \ne 1$, so $g * x * g^{-1} \in S$.
      have hgxs : g * x * g⁻¹ ∈ S :=
        Finset.mem_erase_of_ne_of_mem hgx (Set.mem_toFinset.mpr ((hg x).1 hx))
      -- $S$ has only one element since $H$ has order 2.
      have hs : S.card = 1 := by
        rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr H.one_mem')]
        exact Eq.symm (Nat.eq_sub_of_add_eq' ((Set.toFinset_card H.carrier).trans hH).symm)
      -- As a result, $g * x * g^{-1}$ and $x$ should be the same element in $S$, which means $g * x = x * g$.
      exact mul_eq_of_eq_mul_inv (Finset.card_le_one_iff.mp (le_of_eq hs) hxs hgxs)
  -- Then we show that $C_G(H) \le N_G(H)$. In fact, let $g \in C_{G}(H)$ and $x \in H$.
  · intro g hg x
    constructor
    -- On the one hand, if $x \in H$,
    · intro hx
      -- then $g * x * g^{-1} = x$ since $g \in C_{G}(H)$.
      rw [← (eq_mul_inv_of_mul_eq (hg x hx))]
      -- As a result, $g * x * g^{-1} \in H$ since $x \in H$.
      exact hx
    -- On the one hand, if $g * x * g^{-1} \in H$,
    · intro hx
      -- then $g^{-1} * (g * x * g^{-1}) * g = g * x * g^{-1}$ since $g \in C_{G}(H)$, which means $g * x * g^{-1} = x$.
      have h : g * x * g⁻¹ = x := by
        rw [(eq_mul_inv_of_mul_eq (((Subgroup.inv_mem_iff _).mpr hg) _ hx))]
        group
      rw [← h]
      -- As a result, $x \in H$ since $g * x * g^{-1} \in H$.
      exact hx

/-- Moreover, if $N_{G}(H)=G$ then $H \le Z(G)$. -/
example {G : Type*} [Group G] [DecidableEq G] (H : Subgroup G) [Fintype H] (hH : Fintype.card H = 2) (h : H.normalizer = ⊤) : H ≤ center G := by
  intro x
  -- $C_G(H) = G$ since $N_G(H) = G$ and $N_G(H) = C_G(H)$. As a result, $H \le C(G)$.
  apply centralizer_eq_top_iff_subset.mp <|
    (normalizer_eq_centralizer_of_card_eq_two hH).symm.trans h

end Subgroup



section

-- ID: 1057 (from Abstract Algebra, 3rd Edition, David S. Dummit, Richard M. Foote)

open Subgroup

/-- If $G$ is a group and the center of $G$ is of index $n$, then every conjugacy class has at most $n$ elements. -/
example {G : Type*} [Group G] {n : ℕ} (hn : n ≠ 0) (hc : (center G).index = n) (a : G) : Nat.card (conjugatesOf a) ≤ n ∧ Nat.card (conjugatesOf a) ≠ 0 := by
  -- For every $b \in G$ in the conjugacy class of $a$, there exists $g \in G$ such that $b = g * a * g^{-1}$. So we get a function $f$ sending the conjugacy class of $a$ to $G / Z(G)$.
  let f : conjugatesOf a → G ⧸ (center G) := fun ⟨_, hb⟩ ↦ ⟦Classical.choose (isConj_iff.mp hb)⟧
  -- $f$ is injective since for every $b, c \in G$ in the conjugacy class of $a$, if $f(b) = f(c)$ then $b = g * a * g^{-1} = c$.
  have hf : f.Injective := by
    -- For every $x$, $y$ in the conjugacy class of $a$ such that $f(x) = f(y)$, i.e., $
    intro x y hxy
    apply Subtype.val_inj.mp
    rw [← Classical.choose_spec (isConj_iff.mp x.2), ← Classical.choose_spec (isConj_iff.mp y.2)]
    -- there exists $g \in Z(G)$ such that $y = g * x$.
    let g : G := (Classical.choose (isConj_iff.mp x.2))⁻¹ * Classical.choose (isConj_iff.mp y.2)
    have hy : Classical.choose (isConj_iff.mp y.2) = (Classical.choose (isConj_iff.mp x.2)) * g :=
      (mul_inv_cancel_left _ _).symm
    -- $g * a = a * g$ since $g \in Z(G)$.
    have hga : g * a = a * g := (QuotientGroup.eq.mp hxy).1 a
    -- As a result, $y = g * x = g * a * g^{-1} = a$.
    rw [hy, mul_assoc _ _ a, hga, mul_inv_rev]
    group
  have hcn : (center G).index ≠ 0 := ne_of_eq_of_ne hc hn
  haveI : Nonempty (conjugatesOf a) := ⟨a, mem_conjugatesOf_self⟩
  constructor
  · rw [← hc]
    exact Finite.card_le_of_injective' hf (Mathlib.Tactic.Contrapose.mtr (fun _ ↦ hcn))
  · exact fun h ↦ hcn (Finite.card_eq_zero_of_injective hf h)

end



section

open Polynomial

-- The degree of the polymial $X^4 - X -1$ is equal to $4$.
example : natDegree (X ^ 4 - X - 1 : Polynomial ℤ) = 4 := by
  compute_degree
  · exact Int.zero_ne_one.symm

end
