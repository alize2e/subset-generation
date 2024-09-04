# Formalization of subset generation algorithms with Lean 4.

Uses `leanprover/lean4:v4.11.0-rc1`, and all files are inside a folder called "Subsets" in a project.

BinVal
- functions `binVal` and `binValOne` that treat `Subset n`s as numbers in binary (with the lsb on the left) and output those numbers in base ten
- proofs about `binVal` and `binValOne`
- proof `dec1` which could be helpful to prove termination of `genIt` in first case

ConvertGrayPlainIt and ConvertGrayPlainRec
- ConvertGrayPlainIt
  - functions `φ` and `ψ` such that (although I have not proven this)
    - `(grayIt n).map φ = genIt n`
    - `(genIt n).map ψ = grayIt n`
  - proofs that the compositions of these functions yield the identity
- ConvertGrayPlainRec
  - function `genRec'` that recursively generates `Subset n` in lexicographic order with lsb on right
  - functions `φ'` and `ψ'` such that
    - `(genRec' n).map φ' = (grayRecSlides n)`
    - `(grayRecSlides n).map ψ' = (genRec' n)`
  - proofs of the above equalities, and of
    - `ψ' ∘ φ' = (fun s => s)`
    - `φ' ∘ ψ' = (fun s => s)`

EqTransport
- part of an attempt to prove termination of `genIt`, but this attempt will likely fail because of casting, so unlikely to be useful
- defines an equivalence relation between `Subset n`s and `Subset m`s transported along `n=m`, and some lemmas about that

GrayCodeProof, GrayCodeProofIt, and GrayCodeProofLemmas
- GrayCodeProof: proof that the number of changes between adjacent elements of the output of `grayRecSlides` is exactly 1, which is generalized to `genGray` too
- GrayCodeProofIt: function `grayIt` as below except that it returns a list subtype `{l : List (Subset n) // isGray l}` 
- next steps: prove the same property for `grayLoopless`

GrayIt, GrayItValProof, and GrayLSorry
- GrayIt: iterative function `grayIt` for Gray code generation that is based on "Algorithm G" from p.286 of the Knuth book, with proof of termination
- GrayLSorry: function `grayLoopless` that generates the Gray code following "Algorithm L" outlined on p.290 of the Knuth book, using `sorry` for termination
- GrayItValProof has some functions and lemmas used in GrayIt
- next steps
  - prove termination of `grayLoopless`
  - prove that the output of `grayIt` and `grayLoopless` is the same as that of `genGray` and/or `grayRecSlides`
  - proofs of other properties of `grayIt` and `grayLoopless`

GrayRec, GrayRecComp, and GrayRecSlides
- GrayRec and GrayRecSlides have:
  - a function (`genGray` and `grayRecSlides`, respectively) which generates the Gray code recursively. `genGray` is based on the "algorithm" suggested by (5) on p.283 of the Knuth book, while `grayRecSlides` uses the algorithm from the CSE102 slides
  - a proof that any `Subset n` is in the output of `genGray n`/`grayRecSlides n`
  - a proof that the output of `genGray n`/`grayRecSlides n` is of length 2^n
  - a proof of some sort of symmetry of the helper function
- GrayRecSlides also has
  - a proof that `grayRecSlides` is equivalent to the generation method with xor 11000000... described on p.284 of the Knuth book
  - a proof that there are no duplicates in the output of `grayRecSlides`
- GrayRecComp: proof that `genGray n = grayRecSlides n`

IsoFun and IsoVecB
- functions between `Subset n` and either `Fin n → Bool` or `VecB n` (`VecB := Vect Bool`) whose compositions are the identity function, and therefore show that `Subset n` is isomorphic to `Fin n → Bool` and `VecB n`

PlainItIsh
- function `plainItIsh` that generates subsets in lexicographic order in a somewhat iterative way, similarly to "Algorithm M" from p.282 of the Knuth book, with termination proven

PlainItSorry
- iterative function `genIt` that generates subsets in lexicographic order, and is similar to "Algorithm M" on p.282 of the Knuth book
- includes a potential outline for a proof of termination of `genIt` that works in the first case but depends on `sorry`s in the second, and is unlikely to be doable because of the `cast` when adding to `soFar`
- next steps: as far as I can tell, any method that does not rely on a `cast` would be much slower, so maybe I should revive the somewhat iterative in idea `subsetsItOG` or something along those lines, or pass a `curr : Subset n` as a parameter and edit it despite that being exceedingly slow

PlainRecProofs
- proof that any `Subset n` is in the output of `genRec n`
- proof that the output of `genRec n` is of length 2^n
- proof that there are no duplicates in the list output by `genRec n`

SubsetDef
- definition of `Subset n`
- recursive function `genRec` that generates subsets in lexicographic order
- other functions and proofs that can be useful

SubsetsOfLists
- function that outputs the subset of a list of length n corresponding to a `Subset n`
- function that outputs all subsets of a list

UniqMem
- definition of `UniqMem`
- attempts at proofs involving `UniqMem` (namely in the goal of proving that each `Subset n` occurs in `genRec n` etc. exactly once)
- unnecessary now since I can use List.Nodup

(Note: "the Knuth book" refers to _The Art of Computer Programming, Volume 4A, Combinatorial Algorithms, Part 1_ by Donald E. Knuth.)
