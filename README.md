# Formalization of subset generation with Lean 4.

ConvertGrayPlainIt:
- functions φ and ψ such that (although I have not proven this)
  - (Subset.grayIt n).map Subset.φ == Subset.genIt n
  - (Subset.genIt n).map Subset.ψ == Subset.grayIt n
- proofs that the compositions of these functions yields the identity map
- next steps: edit grayRec (or grayRecSlides) and genRec so that they actually correspond with these functions (lsb is not the same in each),
  and prove how φ and ψ relate the outputs of the grayRec and genRec

EqTransport:
- part of an attempt to prove termination of genIt, but this attempt will likely fail because of casting, so unlikely to be useful
- defines an equivalence relation between "Subset n"s and "Subset m"s transported along n=m, and proves some lemmas about it

GrayCodeProof and GrayCodeProofLemmas:
- proof that the number of changes between adjacent elements of the output of grayRecSlides is exactly 1, which is generalized to genGray too
- last step: figure out how to update Lean so I can remove "sorry_getElem_reverse" and rest of lemmas that should be imported from
  GrayCodeProofLemmas

GrayItSorry, GrayItProof, and GrayItValProof:
- GrayItSorry and GrayItProof have iterative algorithms for Gray code generation with an outline for termination proof with "sorry"s – the
  outline for GrayItSorry is simpler, and that for GrayItProof has more things proved / is further along
- GrayItValProof has some functions and lemmas used in GrayItProof
