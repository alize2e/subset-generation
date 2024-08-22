# Formalization of subset generation with Lean 4.

ConvertGrayPlainIt:
- functions `φ` and `ψ` such that (although I have not proven this)
  - `(Subset.grayIt n).map Subset.φ = Subset.genIt n`
  - `(Subset.genIt n).map Subset.ψ = Subset.grayIt n`
- proofs that the compositions of these functions yields the identity map
- next steps: edit `grayRec` (or `grayRecSlides`) and `genRec` so that they actually correspond with these functions (lsb is not the same in each), and prove how `φ` and `ψ` relate the outputs of `grayRec` and `genRec`

EqTransport:
- part of an attempt to prove termination of `genIt`, but this attempt will likely fail because of casting, so unlikely to be useful
- defines an equivalence relation between `Subset n`s and `Subset m`s transported along `n=m`, and some lemmas about that

GrayCodeProof and GrayCodeProofLemmas:
- proof that the number of changes between adjacent elements of the output of `grayRecSlides` is exactly 1, which is generalized to `genGray` too
- last step: figure out how to update Lean so I can remove `sorry_getElem_reverse` and rest of lemmas that should be imported from GrayCodeProofLemmas

GrayItProof, GrayItSorry, and GrayItValProof:
- GrayItSorry and GrayItProof have an iterative algorithm, `grayIt`, for Gray code generation that is based on "Algorithm G" from page 286 of the Knuth book. They also include an outline for a proof of termination that depends on `sorry`s – the outline in GrayItSorry is simpler, and that in GrayItProof has more proofs / is further along
- GrayItValProof has some functions and lemmas used in GrayItProof
- next steps:
  - continue GrayItProof by trying to figure out why it wants a proof of `(grayVal 1 (cons (!a₀) as)).fst+1 ≤ (grayVal 1 a).fst` rather than of `(grayVal 1 (cons (!a₀) as)).fst+1 ≤ (grayVal 1 (cons (a₀) as)).fst`
  - figure out how to prove stuff about `minLeft1?` to use for a proof of `dec_case_2`
  - finish proving termination

GrayRec, GrayRecComp, and GrayRecSlides
- GrayRec and GrayRecSlides have a:
  - function (`genGray` and `grayRecSlides`, respectively) which generates the Gray code recursively. `genGray` is based on the "algorithm" suggested by (5) on page 283 of the Knuth book, while `grayRecSlides` uses the algorithm from the CSE102 slides
  - proof that any `Subset n` is in the output of `genGray n`/`grayRecSlides n`
  - proof that the output of `genGray n`/`grayRecSlides n` is of length 2^n
  - proof of some sort of symmetry of the helper function
- GrayRecComp: proof that `genGray n = grayRecSlides n`

IsoVecB and IsoFun

(Note: "the Knuth book" refers to _The Art of Computer Programming, Volume 4A, Combinatorial Algorithms, Part 1_ by Donald E. Knuth.)
