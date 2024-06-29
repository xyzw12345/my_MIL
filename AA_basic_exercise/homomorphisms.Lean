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
    intro a b
    calc
      _= α a⁻¹ * α b⁻¹ := by simp only [h a⁻¹, inv_inv, h b⁻¹]
      _= α (a⁻¹ * b⁻¹) := Eq.symm (MonoidHom.map_mul α a⁻¹ b⁻¹)
      _=_ := by simp only [h (a⁻¹ * b⁻¹), mul_inv_rev, inv_inv]
}

example {G : Type*} [hg : Group G] (α : G →* G) (h : ∀ x : G, α x = x⁻¹) : CommGroup G := by
  apply CommGroup.mk
  intro a b
  calc
    _= α a⁻¹ * α b⁻¹ := by simp only [h a⁻¹, inv_inv, h b⁻¹]
    _= α (a⁻¹ * b⁻¹) := Eq.symm (MonoidHom.map_mul α a⁻¹ b⁻¹)
    _=_ := by simp only [h (a⁻¹ * b⁻¹), mul_inv_rev, inv_inv]


example {G : Type*} [hG : Group G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) [cyc : IsCyclic G] : IsCyclic H where
  exists_generator := by
    rcases cyc with ⟨g,hg⟩
    use α g
    intro y
    rcases surj y with ⟨x,hx⟩
    rcases hg x with ⟨n,hn⟩
    have : g ^ n = x := hn
    use n
    show (α g) ^ n = y
    rw [← hx,←this]
    exact Eq.symm (MonoidHom.map_zpow α g n)

example {G : Type*} [hG : CommGroup G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) : CommGroup H := {
  hH with
  mul_comm := by
    intro a b
    rcases surj a with ⟨x,hx⟩
    rcases surj b with ⟨y,hy⟩
    rw [←hx,←hy]
    calc
      _= α (x * y) := by simp only [map_mul]
      _= α (y * x) := by rw [mul_comm]
      _=_ := by simp only [map_mul]
}

example {G : Type*} [hG : CommGroup G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) : CommGroup H := by
  apply CommGroup.mk
  intro a b
  rcases surj a with ⟨x,hx⟩
  rcases surj b with ⟨y,hy⟩
  rw [←hx,←hy]
  calc
    _= α (x * y) := by simp only [map_mul]
    _= α (y * x) := by rw [mul_comm]
    _=_ := by simp only [map_mul]

def squarehom {G : Type*} [CommGroup G] : G →* G where
  toFun := by
    intro x
    use x * x
  map_one' := by group
  map_mul' := by
    intro x y
    dsimp
    calc
      _= x * (y * x) * y := by group
      _= x * (x * y) * y := by simp only [mul_comm]
      _=_ := by group

example {G : Type*} [hG : Group G] (α : G →* G) (h : ∀ g : G , α g = g * g) : CommGroup G := {
    hG with
    mul_comm := by
      intro a b
      calc
        _= a⁻¹ * (a * a) * (b * b) * b⁻¹ := by group
        _= a⁻¹ * (α  a) * (α b) * b⁻¹ := by simp only [h]
        _= a⁻¹ * (α (a * b)) * b ⁻¹ := by simp only [mul_assoc, map_mul]
        _=_ := by simp only [h (a * b)];group
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

noncomputable def iso {G H : Type*} [Group G] [Group H] (α : G →* H) (surj : Function.Surjective α) (inj : Function.Injective α) : G ≃* H where
  toFun := by
    intro x
    use α x
  invFun := by
    intro y
    exact Classical.choose (surj y)
  left_inv := by
    intro x
    show Classical.choose (surj (α x)) = x
    have : α (Classical.choose (surj (α x))) = α x := by
      apply Classical.choose_spec (surj (α x))
    exact inj this
  right_inv := by
    intro y
    show α (Classical.choose (surj y)) = y
    exact Classical.choose_spec (surj y)
  map_mul' := by
    intro x y
    show α (x * y) = α x * α y
    simp only [map_mul]

--kernel
--example {G : Type*} [hG : CommGroup G] [hH : Group H] (α : G →* H) : ∀ a  g : G, a ∈ Ker α → (g * a * g⁻¹) ∈ Ker α := by sorry

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
