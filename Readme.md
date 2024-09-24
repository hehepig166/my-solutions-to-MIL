## resources

* MIL index https://leanprover-community.github.io/mathematics_in_lean/index.html
* MIL source https://github.com/leanprover-community/mathematics_in_lean
* API documentation https://leanprover-community.github.io/mathlib4_docs/
* contrl_space



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
  * 
* 
  test


