import Mathlib

open Set
open Subgroup MonoidHom

/-
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
  -/
