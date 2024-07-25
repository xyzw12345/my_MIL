import Mathlib

open Set
open Subgroup MonoidHom

--homomorphism
def invhom {G : Type*} [CommGroup G] : G →* G where
  toFun := by
    intro x
    use x⁻¹
  map_one' := by group
  map_mul' := by
    intro x y
    show (x * y)⁻¹ = x⁻¹ * y⁻¹
    calc
      _= y⁻¹ * x⁻¹ := by group
      _=_ := by rw [mul_comm]

example {G : Type*} [hg : Group G] (α : G →* G) (h : ∀ x : G, α x = x⁻¹) : CommGroup G := {
  hg with
  mul_comm := by
    sorry
}

example {G : Type*} [hg : Group G] (α : G →* G) (h : ∀ x : G, α x = x⁻¹) : CommGroup G := by
  apply CommGroup.mk
  sorry



example {G : Type*} [hG : Group G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) [cyc : IsCyclic G] : IsCyclic H := sorry

example {G : Type*} [hG : CommGroup G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) : CommGroup H := sorry

example {G : Type*} [hG : Group G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) (sr : ∀ g : G, ∃ g' : G, g = g' * g') : ∀ h : H, ∃ h' : H, h = h' * h' := by
  sorry

def squarehom {G : Type*} [CommGroup G] : G →* G := sorry

example {G : Type*} [hG : Group G] (α : G →* G) (h : ∀ g : G , α g = g * g) : CommGroup G := sorry

example {G G' G'': Type*} [Group G] [Group G'] [Group G''] (α : G →* G') (β : G' →* G'') : G →* G'' := sorry

example {G H : Type*} [Group G] [Group H] (α : G →* H) (A : Set (G × H)) (h : ∀ x : G × H, x ∈ A ↔ x.2 = α x.1): Subgroup (G × H) := sorry

def pre_subgroup {G H : Type*} [Group G] [Group H] (α : G →* H) (H' : Subgroup H) : Set G := {g : G| α g ∈ H'}

def pre_subgroup' {G H : Type*} [Group G] [Group H] (α : G →* H) (H' : Subgroup H) : Subgroup G := sorry

def im_subgroup {G H : Type*} [Group G] [Group H] (α : G →* H) (G' : Subgroup G) : Set H := {h : H| ∃ g : G,(g ∈ G') ∧ (h = α g)}

def im_subgroup' {G H : Type*} [Group G] [Group H] (α : G →* H) (G' : Subgroup G) : Subgroup H := sorry

def inviso' {G : Type*} [hG : CommGroup G] : G ≃* G := {
  invhom with
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

--isomorphism
def inviso {G : Type*} [CommGroup G] : G ≃* G where
  toFun := by
    intro x
    use x⁻¹
  invFun := by
    intro x
    use x⁻¹
  left_inv := by
    intro x
    show (x⁻¹)⁻¹ = x
    group
  right_inv := by
    intro x
    show (x⁻¹)⁻¹ = x
    group
  map_mul' := by
    intro x y
    show (x * y)⁻¹ = x⁻¹ * y⁻¹
    calc
      _= y⁻¹ * x⁻¹ := by group
      _=_ := by rw [mul_comm]

#check Classical.choose

noncomputable def iso {G H : Type*} [Group G] [Group H] (α : G →* H) (surj : Function.Surjective α) (inj : Function.Injective α) : G ≃* H := sorry

def prodiso {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂] (α : G₁ ≃* G₂) (β : H₁ ≃* H₂) : (G₁ × H₁) ≃* (G₂ × H₂) := sorry

def exchangeiso {G H : Type*} [Group G] [Group H] : (G × H) ≃* (H × G) := sorry

--kernel
example {G : Type*} [hG : CommGroup G] [hH : Group H] (α : G →* H) : ∀ a g : G, a ∈ α.ker → (g * a * g⁻¹) ∈ α.ker := by
  sorry

example {G : Type*} [hG : Group G] [hH : CommGroup H] (α : G →* H): ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ α.ker := by sorry

#check eq_bot_iff_forall

example {G : Type*} [hG : Group G] [hH : Group H] (α : G →* H) : Function.Injective α ↔ α.ker = ⊥ := by
  constructor
  · intro inj
    sorry
  · intro h
    sorry

--automorphisms
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

def inner_automorphism {G : Type*} [Group G] (a : G): G ≃* G := sorry

def inner_automrphisms [Group G] : Set (G ≃* G) := {α | ∃ a : G , α = inner_automorphism a}

def inner_automrphisms' [Group G] : Subgroup (MulAut G) := sorry

instance [Group G₀]: (inner_automrphisms' (G := G₀)).Normal := sorry
