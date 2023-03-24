## Algorithms 𝒲 and ℳ in Agda
Implementation of Hindley-Milner type inference algorithms 𝒲 (Milner 1978) and ℳ (Lee
and Yi 1998). Available for reference as algorithms.

## Notice

This project is to aid my own understanding of these algorithms. I chose Agda
because I like it. **I do not claim any formalization of metatheory**. In
particular, I use a named representation (with names ∈ ℕ) under the [Barendregt
convention](https://cs.stackexchange.com/questions/69323/barendregts-variable-convention-what-does-it-mean).

I suspect formalization would not be terribly novel or difficult, but one would
first need to switch variable representation to either DeBruijn or locally
nameless (see Charguéraud (2012)). I would recommend locally nameless, as
algorithms 𝒲 and ℳ require the generation of "new" type variables, which the
locally nameless style provides via "atoms".


## References

- Robin Milner. A theory of type polymorphism in programming. Journal of
  Computer and System Sciences, pages 348–375, 1978

- Luis Damas and Robin Milner. Principal type schemes for functional programs.
  In Proceedings of the 9th ACM SIGPLAN-SIGACT symposium on Principles of
  programming languages, POPL ’82, pages 207–212, Albuquerque, NM, 1982. ACM

- Simplifying and Improving Qualified Types, Mark P. Jones, Research Report
  YALEU/DCS/RR-1040, Yale University, New Haven, Connecticut, USA, June
  1994.

- Mark P. Jones. Formal properties of the Hindley-Milner type system. Personal
  communication, 1995.

- Oukseh Lee and Kwangkeun Yi. Proofs about a folklore let-polymorphic type
  inference algorithm. ACM Trans. Program. Lang. Syst., 20(4):707–723, 1998.
  doi: 10.1145/291891.291892. URL https://doi.org/10.1145/291891.291892

- Arthur Charguéraud. The locally nameless representation. J. Autom. Reason., 49
  (3):363–408, 2012. doi: 10.1007/s10817-011-9225-2

- John C. Reynolds. The meaning of types from intrinsic to extrinsic semantics.
  BRICS Report Series, 7(32), Jun. 2000. doi: 10.7146/brics.v7i32.20167. URL
  https: //tidsskrift.dk/brics/article/view/20167
