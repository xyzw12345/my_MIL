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

example {G : Type*} [hG : Group G] [hH : Group H] (α : G →* H) (surj : Function.Surjective α) (sr : ∀ g : G, ∃ g' : G, g = g' * g') : ∀ h : H, ∃ h' : H, h = h' * h' := by
  intro h
  rcases surj h with ⟨g,hg⟩
  rcases sr g with ⟨g',hg'⟩
  use α g'
  rw [←hg,hg',map_mul]

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

example {G G' G'': Type*} [Group G] [Group G'] [Group G''] (α : G →* G') (β : G' →* G'') : G →* G'' where
  toFun := by
    intro g
    use β (α g)
  map_one' := by simp only [map_one]
  map_mul' := by
    intro a b
    simp only [map_mul]

example {G H : Type*} [Group G] [Group H] (α : G →* H) (A : Set (G × H)) (h : ∀ x : G × H, x ∈ A ↔ x.2 = α x.1): Subgroup (G × H) where
  carrier := A
  mul_mem' := by
    intro a b ha hb
    have ha' : a.2 = α a.1 := (h a).mp ha
    have hb' : b.2 = α b.1 := (h b).mp hb
    apply (h (a * b)).mpr
    simp only [Prod.snd_mul, ha', hb', Prod.fst_mul, map_mul]
  one_mem' := by
    show 1 ∈ A
    apply (h 1).mpr
    simp only [Prod.snd_one, Prod.fst_one, map_one]
  inv_mem' := by
    intro a ha
    have ha' : a.2 = α a.1 := (h a).mp ha
    show a⁻¹ ∈ A
    apply (h a⁻¹).mpr
    simp only [Prod.snd_inv, ha', Prod.fst_inv, map_inv]

def pre_subgroup {G H : Type*} [Group G] [Group H] (α : G →* H) (H' : Subgroup H) : Set G := {g : G| α g ∈ H'}

def pre_subgroup' {G H : Type*} [Group G] [Group H] (α : G →* H) (H' : Subgroup H) : Subgroup G where
  carrier := pre_subgroup α H'
  mul_mem' := by
    intro a b ha hb
    show α (a * b) ∈ H'
    simp only [map_mul]
    exact (Subgroup.mul_mem_cancel_right H' hb).mpr ha
  one_mem' := by
    show α 1 ∈ H'
    simp only [map_one]
    exact Subgroup.one_mem H'
  inv_mem' := by
    intro a ha
    have ha' : α a ∈ H' := ha
    show α a⁻¹ ∈ H'
    simp only [map_inv, inv_mem_iff,ha']

def im_subgroup {G H : Type*} [Group G] [Group H] (α : G →* H) (G' : Subgroup G) : Set H := {h : H| ∃ g : G,(g ∈ G') ∧ (h = α g)}

def im_subgroup' {G H : Type*} [Group G] [Group H] (α : G →* H) (G' : Subgroup G) : Subgroup H where
  carrier := im_subgroup α G'
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨x,hx1,hx2⟩
    rcases hb with ⟨y,hy1,hy2⟩
    use x * y
    simp only [hx2, hy2, map_mul, and_true]
    exact (Subgroup.mul_mem_cancel_right G' hy1).mpr hx1
  one_mem' := by
    use 1
    simp only [map_one, and_true,Subgroup.one_mem G']
  inv_mem' := by
    intro a ha
    rcases ha with ⟨x,hx1,hx2⟩
    use x⁻¹
    simp only [inv_mem_iff, hx1, hx2, map_inv, and_self]

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

def inviso' {G : Type*} [hG : CommGroup G] : G ≃* G := {
  invhom with
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
}

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

def prodiso {G₁ G₂ H₁ H₂ : Type*} [Group G₁] [Group G₂] [Group H₁] [Group H₂] (α : G₁ ≃* G₂) (β : H₁ ≃* H₂) : (G₁ × H₁) ≃* (G₂ × H₂) where
  toFun := by
    intro x
    use (α x.1),(β x.2)
  invFun := by
    intro y
    use (α.invFun y.1),(β.invFun y.2)
  left_inv := by
    intro x
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, EquivLike.coe_symm_apply_apply,Prod.mk.eta]
  right_inv := by
    intro y
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm,MulEquiv.apply_symm_apply, Prod.mk.eta]
  map_mul' := by
    intro x₁ x₂
    simp only [Prod.fst_mul, map_mul, Prod.snd_mul, Prod.mk_mul_mk]

def exchangeiso {G H : Type*} [Group G] [Group H] : (G × H) ≃* (H × G) where
  toFun := by
    intro x
    use x.2,x.1
  invFun := by
    intro y
    use y.2,y.1
  left_inv := by
    intro x
    simp only [Prod.mk.eta]
  right_inv := by
    intro y
    simp only [Prod.mk.eta]
  map_mul' := by
    intro x₁ x₂
    simp only [Prod.snd_mul, Prod.fst_mul, Prod.mk_mul_mk]

--kernel
example {G : Type*} [hG : CommGroup G] [hH : Group H] (α : G →* H) : ∀ a g : G, a ∈ α.ker → (g * a * g⁻¹) ∈ α.ker := by
  intro a g ha
  have : α a = 1 := ha
  show α (g * a * g⁻¹) = 1
  calc
    _= α g * α a * α g⁻¹ := by simp only [map_mul]
    _=_ := by simp [this]

example {G : Type*} [hG : Group G] [hH : CommGroup H] (α : G →* H): ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ α.ker := by
  intro x y
  show α (x * y * x⁻¹ * y⁻¹) = 1
  calc
    _= α x * α y * (α x)⁻¹ * (α y)⁻¹ := by simp only [map_mul,map_inv]
    _= α y * α x * (α x)⁻¹ * (α y)⁻¹ := by simp only [mul_comm]
    _=_ := by simp only [mul_inv_cancel_right, mul_right_inv]

#check eq_bot_iff_forall
--#check ker_eq_bot_iff
example {G : Type*} [hG : Group G] [hH : Group H] (α : G →* H) : Function.Injective α ↔ α.ker = ⊥ := by
  constructor
  · intro inj
    have : ∀ g ∈ α.ker, g = 1 := by
      intro g hg
      have : α g = 1 := hg
      have : α g = α 1 := by simp only [this, map_one]
      exact inj this
    apply (eq_bot_iff_forall α.ker).mpr this
  · intro h
    have h': ∀ g ∈ α.ker, g = 1 := (eq_bot_iff_forall α.ker).mp h
    intro a b heq
    have : a * b⁻¹ ∈ α.ker := by
      show α (a * b⁻¹) = 1
      calc
        _= α a * (α b)⁻¹ := by simp only [map_mul, map_inv]
        _=_ := by simp only [heq, mul_right_inv]
    have : a * b⁻¹ = 1 := h' (a * b⁻¹) this
    calc
      _= a * b⁻¹ * b := by group
      _=_ := by simp only [this, one_mul]

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

def inner_automorphism {G : Type*} [Group G] (a : G): G ≃* G where
  toFun := by
    intro g
    use a * g * a⁻¹
  invFun := by
    intro g
    use a⁻¹ * g * a
  left_inv := by
    intro g
    group
  right_inv := by
    intro g
    group
  map_mul' := by
    intro g h
    group

def inner_automrphisms [Group G] : Set (G ≃* G) := {α | ∃ a : G , α = inner_automorphism a}

def inner_automrphisms' [Group G] : Subgroup (MulAut G) where
  carrier := inner_automrphisms
  mul_mem' := by
    intro α β hα hβ
    rcases hα with ⟨a,ha⟩
    rcases hβ with ⟨b,hb⟩
    use a * b
    ext g
    rw [ha,hb]
    unfold inner_automorphism
    dsimp
    group
  one_mem' := by
    use 1
    ext g
    unfold inner_automorphism
    dsimp
    group
  inv_mem' := by
    intro α hα
    rcases hα with ⟨a,ha⟩
    use a⁻¹
    ext g
    unfold inner_automorphism
    simp only [inv_inv, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    have : α (α⁻¹ g) = α (a⁻¹ * g * a) := by
      simp only [MulAut.apply_inv_self]
      rw [ha]
      unfold inner_automorphism
      dsimp
      group
    apply MulEquiv.injective α this

instance [Group G₀]: (inner_automrphisms' (G := G₀)).Normal where
  conj_mem := by
    intro α hα β
    rcases hα with ⟨a,ha⟩
    use β a
    ext g
    rw [ha]
    unfold inner_automorphism
    dsimp
    simp only [map_mul, MulAut.apply_inv_self, map_inv]
