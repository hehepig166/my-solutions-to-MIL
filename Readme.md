## resources

* MIL index https://leanprover-community.github.io/mathematics_in_lean/index.html
* MIL source https://github.com/leanprover-community/mathematics_in_lean
* API documentation https://leanprover-community.github.io/mathlib4_docs/
* contrl_space
* https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
* The Mechanics of Proof https://hrmacbeth.github.io/math2001/index.html
* Theorem Proving in LEAN4 https://leanprover.github.io/theorem_proving_in_lean4/



## tatics

* `rw`
* `exact`, `apply`
* `simp`, `dsimp`
* `calc`
* `trans`
* `cases`, `cases'`



## C02 Basics

* S01 Calculating
  * `rw`
  * `exact`
  
* S02 Proving Identities in Algebraic Structures
  * `apply`
  * `rfl`
  * `ring`
  * `have`
  * `norm_num`
  * `[AddGroup A], [CommGroup], [AddCommGroup]`
  
* S03 Using Theorems and Lemmas
  *  `apply`: tries to match the conclusion with the current goal, and leaves the hypotheses, if any, as new goals
  * `.`: within the block introduced by the dot, only one goal is visible, and it must be completed before the end of the block.
  * `linarith`
  * `h.mp`, `h.mpr` (`h.1`, `h.2`)
    * `h : A <-> B`
    * `h.mp : A -> B`
    * `h.mpr : B -> A`
  * `norm_num` can be used to solve concrete numeric goals
  * `apply?`
  * Ctrl-space
  * In Lean, a theorem named `A_of_B_of_C` establishes something of the form `A` from hypotheses of the form `B` and `C`, where `A`, `B`, and `C` approximate the way we might read the goals out loud
  * refine / exact / apply ?
  * Mathlib tends to favor `≤` over `≥`
  * `linarith`
  * use `constructor` tactic to split a conjunction to two goals
  
* S04 More examples using apply and rw
  * currying
  * `show`
  * `intro`
  * `repeat`
  * `x ∣ y`, dvd
  * `gcd`, `lcm`
  
* S05 Proving Facts about Algebraic Structures
  * partial order, `[PartialOrder α]`, `≤`
    * reflexive, `le_refl x : x ≤ x`
  
    * transitive, `le_trans : x ≤ y → y ≤ z → x ≤ z`

    * antisymmetric, `le_antisymm : x ≤ y → y ≤ x → x = y`
  
  * strict partial order, `<`
  
  * `abbrev`/ `def`
  
  * `variable {α : Type*} [Lattice α]
    * A *lattice* is a structure that extends a partial order with operations `⊓` and `⊔` that are analogous to `min` and `max` on the real numbers:
    * `⊓`: `\inf` or `\glb`, greatest lower bound
    * `⊔`: `\sup` or `\lub`, least upper bound
    * `min` and `max` on any total order, such as the integers or real numbers with `≤`
    * `∩` and `∪` on the collection of subsets of some domain, with the ordering `⊆`
    * `∧` and `∨` on boolean truth values, with ordering `x ≤ y` if either `x` is false or `y` is true
    * `gcd` and `lcm` on the natural numbers (or positive natural numbers), with the divisibility ordering, `∣`
    * the collection of linear subspaces of a vector space, where the greatest lower bound is given by the intersection, the least upper bound is given by the sum of the two spaces, and the ordering is inclusion
    * the collection of topologies on a set (or, in Lean, a type), where the greatest lower bound of two topologies consists of the topology that is generated by their union, the least upper bound is their intersection, and the ordering is reverse inclusion
  
  * priority : ⊓ > ⊔
    
  * `calc`
  
  * `trans`
  
  * `variable {α : Type*} [DistribLattice α]`
  
  * `variable {X : Type*} [MetricSpace X]`
    * A *metric space* consists of a set equipped with a notion of distance, `dist x y`, mapping any pair of elements to a real number.
  
  
  
  
## C03



## C04



## C05



## C06 Structures

* S01 Defining structures

  * An *instance* of the structure is a particular bundle of data satisfying the constraints.

  * ```
    structure Point where
      x : ℝ
      y : ℝ
      z : ℝ
    ```

  * `@[ext]`, extensionality

  * the constructor for a structure

  * functions on structures

  * anonymous projection notation, `a.add b` instead of `Point.add a b`

  * `protected`

  * pattern matching

  * `noncomputable section`

  * Structures can depend on parameters.
  
  * `Finset.sum_add_distrib`, `Finset.mul_sum`
  
  * products
  
    * `def Point'' := ℝ × ℝ × ℝ`
  
  * subtype construction
  
    * `def PReal := { y : Real // 0 < y}`
    * `PReal.val, PReal.property`
  
  * Sigma types
  
    * generalizations of ordered pairs
  
    * `def StdSimplex := Σ n : ℕ, StandardSimplex n`
  
    * `.fst`, `.snd`
  
  * using structures has a number of advantages

* S02 Algebraic Structures

  * carrier set

  * algebraic structures lead dual lives in mathematics, as containers for collections of objects and as objects in their own right.

  * `#print Group`
  
  * `structure GroupCat`
  
  * ```Lean
    variable (f : α ≃ β) (g : β ≃ γ)
    
    #check Equiv α β
    
    #check (f.toFun : α → β)
    #check (f.invFun : β → α)
    #check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
    #check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
    
    #check (Equiv.refl α : α ≃ α)
    #check (f.symm : β ≃ α)
    #check (f.trans g : α ≃ γ)
    ```
  
    ```
    example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
      rfl
    
    example (x : α) : (f.trans g) x = g (f x) :=
      rfl
    
    example : (f.trans g : α → γ) = g ∘ f :=
      rfl
    ```
  
  * `Equiv.perm`
  
  * `Group` -> `mul`, `one`, `inv`
  
  * `AddGroup` -> `add`, `zero`, `neg`
  
  * associate notation with structures -> use it with any particular instance
  
  * `()`, `{}`, `[]`
  
    * When we use the anonymous square-bracket annotation with the `variables` command, then as long as the variables are still in scope, Lean automatically adds the argument `[Group G]` to any definition or theorem that mentions `G`.
  
  * `class - instance`
  
  * `structure - def`
  
