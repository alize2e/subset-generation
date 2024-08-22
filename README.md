# Formalization of subset generation with Lean 4.

BinVal
- functions `binVal` and `binValOne` that treat `Subset n`s as numbers in binary (with the lsb on the left) and output those numbers in base ten
- proofs about `binVal` and `binValOne`
- proof `dec1` which could be helpful to prove termination of `genIt` in first case

ConvertGrayPlainIt
- functions `φ` and `ψ` such that (although I have not proven this)
  - `(Subset.grayIt n).map Subset.φ = Subset.genIt n`
  - `(Subset.genIt n).map Subset.ψ = Subset.grayIt n`
- proofs that the compositions of these functions yields the identity map
- next steps: edit `grayRec` (or `grayRecSlides`) and `genRec` so that they actually correspond with these functions (lsb is not the same in each), and prove how `φ` and `ψ` relate the outputs of `grayRec` and `genRec`

EqTransport
- part of an attempt to prove termination of `genIt`, but this attempt will likely fail because of casting, so unlikely to be useful
- defines an equivalence relation between `Subset n`s and `Subset m`s transported along `n=m`, and some lemmas about that

GrayCodeProof and GrayCodeProofLemmas
- proof that the number of changes between adjacent elements of the output of `grayRecSlides` is exactly 1, which is generalized to `genGray` too
- last step: figure out how to update Lean so I can remove `sorry_getElem_reverse` and rest of lemmas that should be imported from GrayCodeProofLemmas

GrayItProof, GrayItSorry, and GrayItValProof
- GrayItSorry and GrayItProof have an iterative algorithm, `grayIt`, for Gray code generation that is based on "Algorithm G" from p. 286 of the Knuth book. They also include an outline for a proof of termination that depends on `sorry`s – the outline in GrayItSorry is simpler, and that in GrayItProof has more proofs / is further along
- GrayItValProof has some functions and lemmas used in GrayItProof
- next steps:
  - continue GrayItProof by trying to figure out why it wants a proof of `(grayVal 1 (cons (!a₀) as)).fst+1 ≤ (grayVal 1 a).fst` rather than of `(grayVal 1 (cons (!a₀) as)).fst+1 ≤ (grayVal 1 (cons (a₀) as)).fst`
  - figure out how to prove stuff about `minLeft1?` to use for a proof of `dec_case_2`
  - finish proving termination

GrayRec, GrayRecComp, and GrayRecSlides
- GrayRec and GrayRecSlides have:
  - a function (`genGray` and `grayRecSlides`, respectively) which generates the Gray code recursively. `genGray` is based on the "algorithm" suggested by (5) on p. 283 of the Knuth book, while `grayRecSlides` uses the algorithm from the CSE102 slides
  - a proof that any `Subset n` is in the output of `genGray n`/`grayRecSlides n`
  - a proof that the output of `genGray n`/`grayRecSlides n` is of length 2^n
  - a proof of some sort of symmetry of the helper function
- GrayRecComp: proof that `genGray n = grayRecSlides n`

IsoFun and IsoVecB
- functions between `Subset n` and either `Fin n → Bool` or `VecB n` (`VecB := Vect Bool`) whose compositions are the identity function, and therefore show that `Subset n` is isomorphic to `Fin n → Bool` and `VecB n`

PlainItSorry
- iterative function `genIt` that generates subsets in lexicographic order, and is similar to "Algorithm M" on p. 282 of the Knuth book
- includes a potential outline for a proof of termination of `genIt` that works in the first case but depends on `sorry`s in the second, and is unlikely to be doable because of the `cast` when adding to `soFar`

PlainRecProofs
- a proof that any `Subset n` is in the output of `genRec n`
- a proof that the output of `genRec n` is of length 2^n

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
- probably unnecessary / a lot easier if I manage to update Lean and gain access to some of the newer theorems and definitions, especially Nodup

(Note: "the Knuth book" refers to _The Art of Computer Programming, Volume 4A, Combinatorial Algorithms, Part 1_ by Donald E. Knuth.)
