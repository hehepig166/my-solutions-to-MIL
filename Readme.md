## resources

* MIL index https://leanprover-community.github.io/mathematics_in_lean/index.html
* MIL source https://github.com/leanprover-community/mathematics_in_lean
* API documentation https://leanprover-community.github.io/mathlib4_docs/
* contrl_space



## tatics

* `rw`
* ``



## C02

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
  
  * `variable {α : Type*} [Lattice α]`
    * A *lattice* is a structure that extends a partial order with operations `⊓` and `⊔` that are analogous to `min` and `max` on the real numbers:
    * `⊓`: `\inf` or `\glb`, greatest lower bound
    * `⊔`: `\sup` or `\lub`, least upper bound
    * `min` and `max` on any total order, such as the integers or real numbers with `≤`
    * `∩` and `∪` on the collection of subsets of some domain, with the ordering `⊆`
    * `∧` and `∨` on boolean truth values, with ordering `x ≤ y` if either `x` is false or `y` is true
    * `gcd` and `lcm` on the natural numbers (or positive natural numbers), with the divisibility ordering, `∣`
    * the collection of linear subspaces of a vector space, where the greatest lower bound is given by the intersection, the least upper bound is given by the sum of the two spaces, and the ordering is inclusion
    * the collection of topologies on a set (or, in Lean, a type), where the greatest lower bound of two topologies consists of the topology that is generated by their union, the least upper bound is their intersection, and the ordering is reverse inclusion
  
  * `calc`
  
  * `trans`
  
* test

