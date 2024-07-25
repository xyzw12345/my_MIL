import Mathlib

set_option autoImplicit true

/-!

## The main goal of this section
A (very) brief introduction to `Equivalence` in LEAN
A brief introduction to `cosets` in LEAN and one example regarding this concept
A brief introduction to `QuotientGroup` in LEAN

# About `Equivalence` in mathematics
An equivalence relation is a binary relation r that is
  ⬝ reflexive (`refl` in LEAN): ∀ x, r x x
  ⬝ symmetric (`symm` in LEAN): ∀ {x y}, r x y → r y x
  ⬝ transitive (`trans` in LEAN): ∀ {x y z}, r x y → r y z → r x z

Suitable and trivial examples regarding equivalence include:
  ⬝ equality
  ⬝ matrices being similar or congruent
  ⬝ in abrstract algebra, many others

Try looking it up in Mathlib files may be helpful when determining which theorem(s) to use when formalising problems, not only in abstract algebra. Command + click on `iseqv` in the following example to find out about `iseqv` and more. Or try this: `#check Setoid.iseqv` for more information.

We are now looking into a more specific example of equivalence. All of the information below can be found easily by Command + placing your cursor onto the term.

  ⬝ A setoid is a type with a distinguished equivalence relation, denoted `≈`. This is mainly used as input to the `Quotient` type constructor.

  ⬝ A Monoid is a Semigroup with an element 1 such that 1 * a = a * 1 = a.

  ⬝ A submonoid of a monoid M is a subset containing 1 and closed under multiplication.

  ⬝ A commutative monoid is a monoid with commutative (`*`).

Now a relation `r` is constructed as below. We want to use `r` to construct a `Setoid` structure on a `CommMonoid`, i. e., we need to prove `r` is an equivalence relation. Note that, `Setoid` is a `class` containing `r` and `iseqv`, which requires us to point `r` out directly as well as putting forward a proof of equivalence. However,
`Equivalence` is also a structure containing the three elements mentioned above. That requires a proof for each of the elements.

The key for this problem in MIL is rather short because it uses one-line short proof a lot. However, as we want to show the process of proof more clearly, we will mostly not adopt this style of proof in this section.

-/

section Equivalence

#check Equivalence
#check Setoid.iseqv

def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x * w = y * z
  -- We will suppose `r` is a given relation and focus on proving the rest.
  iseqv := {
    refl := by
      -- By `intro` we are able to bring in a variable `a` for clarity of statement.

      -- A trick in the lecture of logic in LEAN should have mentioned that a proper tool for a existence statement is to find a proper value that satisfies the statement, namely `use` a value. By observation we can find that when `w` and `z` are both `1` in `N`, the statement is satisfied and proof most simple.

      -- Use `constructor` to divide the goal into two parts.

      -- If you have not looked up the directory for this part, try `apply?` or `simp?` for some possible help.

      -- Now we have the same problem once again, solved using the trick above.
      sorry
    -- a simpler proof for this: `refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩`
    symm := by

      -- Another way to deal with existence statement in the conditions is that you can `rcases` the statement into multiple conditions to simplify the proof.

      -- From `eq` you should be able to know what to `use`.
      sorry
    -- a simpler proof for this: `symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩`
    trans := by
      intro _ _ a cond_eq₁ cond_eq₂
      rcases cond_eq₁ with ⟨b, b_in_N, c, c_in_N, eq₁⟩
      rcases cond_eq₂ with ⟨d, d_in_N, e, e_in_N, eq₂⟩
      -- or better: `rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩`

      -- a simpler proof to reach this goal: `refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩`
      -- Now it becomes a matter of patience to finetune this expression with `rw`.
      sorry
  }

-- Once an equilvalence is proved, we can use the properties by the theorems below. Check them out by `#check` and see the expressions of them.
#check Setoid.refl
#check Setoid.symm
#check Setoid.trans

end Equivalence

/-！

# Cosets in LEAN

For convenience of this section we will first only discuss left cosets on `•` groups. For right cosets and `AddGroup`s please refer to the documentation using the tricks mentioned above. We will only introduce the theorems useful in the example below, and more are left for further research and discovery (possibly invention).

When `G` is a group and `a : G`, `s : Set G`, with  `open scoped Pointwise` we can write the left coset of `s` by `a` as `a • s`.

-/

#check mem_leftCoset_iff

-- One more useful theorem about the property of equal sets. You could have seen it already if you have ever played Set Theory Game.

#check Set.Subset.antisymm_iff

section Coset

open scoped Pointwise
open Function MulOpposite Set

variable {α : Type*}
variable [Mul α]

#check leftCosetEquivalence_rel

/-- Equality of two left cosets `a * s` and `b * s`. -/
theorem MyLeftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s) := by
  -- `unfold` helps you simplify the statement to more basic ones.
  unfold LeftCosetEquivalence
  -- Remember from last section the three elements of `Equivalence`?
  constructor
  -- `refl` part of the proof. Remember how to deal with `∀`?
  sorry
  -- `symm` part of the proof.
  sorry
  -- `trans` part of the proof.
  sorry

#check rightCosetEquivalence_rel

/-- Equality of two right cosets `s * a` and `s * b`. -/
-- Following the example above, the opposite side should not be difficult. Try it as you like. As you try, pick up `op`, the way to express right cosets.
theorem MyRightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence s) := by sorry

variable [Group G]
variable (H: Subgroup G)

-- Left and right cosets of subgroup $H$ are equal if and only if $H$ is normal.
#check normal_iff_eq_cosets

/-- If a subgroup $H$ of $G$ satisfies for all $h \in H$, $g \in G$, $g * h * g⁻¹ \in H$, then the left and right cosets are equal. -/
theorem practice₁ (prop: ∀ (h: H), ∀ (g: G), g * h * g⁻¹ ∈ H): ∀ (g : G),  g • (H : Set G) = op g • (H : Set G) := by
  -- Notice that `prop` looks very similar to the definition of normal subgroups. We can prove it using `have` to introduce an intermediate statement.
  have: H.Normal := by
    -- Sometimes `apply?` can return confusing results containing `refine` or other things. But some can be used to simplify the statement. Here we just adopt it.

    -- The goal is very close to `prop` now. See the difference?
    sorry
  -- Now use the theorem `#check`ed out to close the goal.
  sorry

-- To subset $H$ of group $G$, element $x \in a * H$ if and only if $a⁻¹ * x \in H.$
#check mem_leftCoset_iff

/-- Set $H₁$ and $H₂$ to be subgroups of $G$. Prove that any left coset of $H₁\cap H₂$ is an intersection of one left coset of $H₁$ and one left coset of $H₂$. -/
theorem practice₂: ∀ (a : G), ∃ (b c : G), (b • ((H₁: Subgroup G) : Set G)) ∩ (c • ((H₂: Subgroup G) : Set G)) = a • (H₁ ∩ H₂: Set G) := by
  -- A common way to cope with `∀` is to introduce a variable to simplify the statement. Here we choose the notation `d` for this variable.
  intro d
  -- For `∃`s, we know that we should `use` something.

  -- If two sets `A` and `B` are equal, then `A ⊆ B ∧ B ⊆ A`. We choose this form because we can further simplify the statement by introducing more variables toget rid of the logics.

  -- Divide the `∧` statement.

  -- We can see that we can `intro` something to make the statement explicit. Remember that intersections can be simplified into two statements - if `x ∈ A ∩ B`, then `x ∈ A ∧ x ∈ B`. To see this more clearly, try using the `simp?` tactic to simplify the statement `h` a bit.

  -- The next step is complex. We finish these tasks at once:
    -- ⬝ `h₁` transformed into `d⁻¹ * x ∈ H₁` by `(mem_leftCoset_iff d).mp`
    -- ⬝ `h₂` transformed into `d⁻¹ * x ∈ H₂` by `(mem_leftCoset_iff d).mp`
    -- ⬝ goal transformed into `d⁻¹ * x ∈ ((H₁ : Set) ∩ (H₂ : Set))` by `(mem_leftCoset_iff d).mpr`
    -- ⬝ New goal closed at once with the combination of the new conditions
  -- If you do not feel comfortable with this expression, using the old style (writing out all `have`s and `apply` them) should do as well.

  -- With the experience above, the opposite direction should not be difficult.
  sorry

end Coset

section Quotient

-- Our first example comes from MIL on quotient monoids. We will show that for commutative monoid $M$ and its submonoid $N$, $M ⧸ N$ is a monoid.

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

--  If `a` and `b` are related by the equivalence relation, then they have equal equivalence classes.
#check Quotient.sound

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  -- Find out what is in a `monoid`.
  -- We aim to prove that this mulplication on the quotient monoid is well-defined, namely if `a₁ * N = b₁ * N`, `a₂ * N = b₂ * N`, then `a₁ * a₂ * N = b₁ * b₂ * N`.
  mul := Quotient.map₂' (· * ·) (by
    -- Does this goal look familiar?
    -- If you have questions about this line, try to `intro` stuff first and then `rcases` them if possible. You will find that the two methods are equivalent.

    -- If you need to, `simp` it.
    -- simp only
    -- Remember the definition and properies of `Setoid`? We now need to prove that there exists an `x` and a `y` such that `a₁ * a₂ * x = b₁ * b₂ * y`. For `∃` statements, what do we do?

    -- First prove that `w * w'` is in `N`. Search for the theorem needed.

    -- Follow the same logic, we can get a simplified equation.

    -- A shorter proof: refine ⟨w * w', N.mul_mem hw hw', z * z', N.mul_mem hz hz', ?_⟩
    -- Practise your patience now playing with `rw`.
    sorry)
  mul_assoc := by

    -- Notice that this equation is about equivalence classes. Try to use the theorem `#check`ed out to transform is into an equation of elements.

    -- Remember the `refl` property of an equivlance relation?
    sorry
  -- The `1` in the quotient monoid is defined as the image of `1` in the monoid under the map of `mk : M → M ⧸ N`. Now following the same logic, it is not hard to prove the following two properties of a monoid. Thus we have a structure of monoid estabilished on `M ⧸ N`.
  one := QuotientMonoid.mk N 1
  one_mul := by
    sorry
  mul_one := by
    sorry

variable [Group G] (H : Subgroup G)

-- The equivalence relation corresponding to the partition of a group by left cosets of a subgroup : `@Setoid.r _ (leftRel s) x y ↔ x⁻¹ * y ∈ s`.
#check QuotientGroup.leftRel
-- The equivalence relation corresponding to the partition of a group by right cosets of a subgroup : `@Setoid.r _ (rightRel s) x y ↔ y * x⁻¹ ∈ s`.
#check QuotientGroup.rightRel
-- Right cosets are in bijection with left cosets: `Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s`.
#check QuotientGroup.quotientRightRelEquivQuotientLeftRel
-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s`.
#check Subgroup.groupEquivQuotientProdSubgroup
-- If `H ≤ K`, then `G / H ≃ G / K × K / H`.
#check Subgroup.quotientEquivProdOfLE

open QuotientGroup

variable [CommGroup P]

#check QuotientGroup.Quotient.commGroup

-- We aim to prove that the quotient group of an Abelian group is Abelian, although it is already an `instance` and can be auto-sloved by LEAN, like this.
theorem prctice₃ {N: Subgroup P} {a b : P ⧸ N}: a * b = b * a := CommGroup.mul_comm a b

instance MyCommGroupQuotientGroup {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  -- An Abelian group is a group, as well as Abelian. As the group part is trivial, we only need to prove the latter, although using a `constructor`.
  constructor

  -- Still we use the same trick to simplify the statement.

  -- Use the condition that `a * b = b * a` with `rw`.
  sorry

-- This lemma comes from Mathlib, and is actually trivial. We present it just to discuss the usage of certain theorems.
#check Quotient.eq
-- `Quotient.mk s a = Quotient.mk s b → a ≈ b`.
#check Quotient.exact
-- `a ≈ b → Quotient.mk s a = Quotient.mk s b`. Compare the two.
#check Quotient.sound

theorem practice₄ {a b : G} : (a : G ⧸ H) = b ↔ a⁻¹ * b ∈ H := by
  -- With some `if and only if` problems it is better to use `constructor` to divide the statement into two sides.
  constructor

  -- Remember the equivalence `#check`ed out above?

  -- Which side should we use?
  sorry
  sorry

variable (N : Subgroup G) [nN : N.Normal]

-- This one is also trivial.
#check eq_one_iff

theorem practice₅ {N : Subgroup G} [nN : N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N := by
  constructor

  -- Use the conclusion from above.
  sorry
  -- Try the opposite side using the same technique.
  sorry

-- From the statements above we can conclude the kernel of the group homomorphism from `G` to `G / N` is `N`.
theorem practice₆ : MonoidHom.ker (QuotientGroup.mk' N : G →* G ⧸ N) = N := sorry

-- Lagrange's Theorem is also in Mathlib. We now describe its proof in LEAN briefly.
/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
theorem LagrangeTheorem [Fintype G] (H : Subgroup G) [DecidablePred (· ∈ H)] : Fintype.card (G ⧸ H) ∣ Fintype.card G := by
  have: Fintype.card G = Fintype.card (G ⧸ H) * Fintype.card H := by
    -- `Fintype.card (α × β) = Fintype.card α * Fintype.card β`

    -- The first states that `Fintype.card α = Fintype.card β`. Note that `congr` means taking the `f` out of `f x = f y` to obtain `x = y`. The second is just the equivalence `#check`ed out above.
    sorry
  rw [this]
  simp only [dvd_mul_right]

variable [Group G][G_cyc: IsCyclic G]
variable (H: Subgroup G) [H.Normal]
open QuotientGroup

-- A quotient group of a cyclic group is cyclic. Here we will not go into details about the subgroup is normal naturally, as our attention is on the quotient propeties.
theorem practice₇: IsCyclic (G ⧸ H) := by
  constructor
  -- Name the generator of `G` as `G_cyc`.
  rcases G_cyc with ⟨G_cyc, l⟩
  -- Take out the image of `G_cyc` under mapping `mk`. This is the generator we propose for the cyclic quotient group.

  -- Take out the `u_index` to `use`.

  -- It can be observed that the two sides are just the equation generated above but under `mk` mapping.

  -- Remember the `congr` mentioned? It is a tactic.

  sorry
  -- or `exact congrArg mk eq`

end Quotient
