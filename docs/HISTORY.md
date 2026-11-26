# History of the proof

[日本語](HISTORY.ja.md)

Each row is one commit. Every commit is a complete proof of the theorem: it builds, and the final theorem depends only on the standard axioms.
The size counts the Lean files under `lean/Tetrahedral/`. A larger size can mean that an argument was written out in more detail.
Commits that do not change the Lean proof are not listed.

| # | Date | Commit | Change | Files | Lines |
|---:|---|---|---|---:|---:|
| 1 | 2026-11-24 | `890476e` | The first complete proof. Five systems, direct quadratic parameters, an element of relative norm 11, division by 11 and relative units. The exponents are found by sieves modulo odd primes and one Skolem-type argument. | 45 | 4,913 |
| 2 | 2026-11-24 | `942b095` | For d = 1, 3, 11, the odd-prime sieves are replaced by one 2-adic descent. | 45 | 4,464 |
| 3 | 2026-11-25 | `b035dc1` | d = 2 is also decided 2-adically, using the original condition that n + 3 is twice a square. | 45 | 4,264 |
| 4 | 2026-11-25 | `e9220b6` | d = 66 is also decided 2-adically; its double root is handled through the relative norm. No odd-prime argument for the exponents remains. | 45 | 4,174 |
| 5 | 2026-11-25 | `4741201` | The relative norm is kept in the error terms, so every branch needs fewer residue classes of the exponent. | 47 | 4,613 |
| 6 | 2026-11-25 | `3d882e2` | The square of the direction and a scalar remainder are kept separately in the error terms, so W can be a smaller power of ρ. | 48 | 4,587 |
| 7 | 2026-11-25 | `8252717` | Negative signs are excluded first, because the first coordinate of every element of the orbit is nonnegative. | 50 | 4,744 |
| 8 | 2026-11-25 | `8ef2337` | For d = 66, the double root is excluded by the original square condition instead of a separate descent. | 51 | 4,683 |
| 9 | 2026-11-25 | `7e7c46d` | For d = 2, the two close roots 0 and −4 are separated from the root −1, for which a smaller power of ρ suffices. | 51 | 4,739 |
| 10 | 2026-11-25 | `6d12596` | For d = 2, a table of residues is replaced by the congruence f(ξ₀ρᵐ) ≡ 32m(m+1) mod 128, proved by third differences. | 52 | 4,725 |
| 11 | 2026-11-25 | `6ae09f0` | An unused parity condition is removed. | 52 | 4,724 |
| 12 | 2026-11-25 | `10de361` | The descents at simple roots go through a small integer lattice and four basis elements. | 53 | 4,663 |
| 13 | 2026-11-25 | `75066d5` | The divisibility of the error terms is derived from the parity of the derivative of the norm. | 53 | 4,674 |
| 14 | 2026-11-25 | `cbd051a` | For d = 11 and 66, the relative conjugation identifies two roots that give the same n; nine base points remain. | 55 | 4,729 |
| 15 | 2026-11-25 | `bc69bde` | The generation of relative units is unified, and decimal approximations are replaced by bounds from the conjugates. | 56 | 4,598 |
| 16 | 2026-11-25 | `c8370dd` | The divisibility constant h and the parity character are derived from the norm-one equation of the unit W. | 58 | 5,005 |
| 17 | 2026-11-25 | `0eda7e7` | The extra divisibility of the scalar term is derived from relative norms and congruences preserved along the orbit. | 58 | 5,365 |
| 18 | 2026-11-25 | `a0c5ff1` | For h = 2, the condition on the derivative at the base points is derived from the two norm equations. | 58 | 5,551 |
| 19 | 2026-11-25 | `baaa380` | Declarations that the final theorem does not use are removed. | 58 | 5,332 |
| 20 | 2026-11-25 | `a0aa0dd` | The theorem is stated at the top level as `Tetrahedral.tetrahedral_classification`, and the comments are corrected. | 58 | 5,331 |
| 21 | 2026-11-26 | `bed02d4` | The theorem is restated with the exact rational quotient and renamed `Tetrahedral.tetrahedral_add_one_eq_sq_iff`. | 58 | 5,332 |
| 22 | 2026-11-25 | `6857813` | For h = 4, the condition on the derivative at the base points is derived from congruences preserved along the orbit. | 58 | 5,715 |
| 23 | 2026-11-25 | `23b22b2` | The derivative is reduced to a product of the two relative coordinates; the conditions on the directions are used only at the end. | 58 | 5,665 |
| 24 | 2026-11-26 | `157f936` | For h = 2, the norm-square identities are replaced by the parity of one coefficient of the relative norm. | 58 | 5,650 |
| 25 | 2026-11-26 | `e48755b` | The congruences f ≡ K ≡ 0 mod 4 are proved for the whole orbit, so the estimates no longer assume exact roots. | 58 | 5,717 |
| 26 | 2026-11-26 | `07d608d` | The higher error terms are controlled by values modulo 2 only. | 58 | 5,714 |
| 27 | 2026-11-26 | `ed9cf54` | In the proof that ρ generates the relative units, the gap between units is replaced by an upper bound for the trace and a positive definite quadratic form. | 57 | 5,518 |
| 28 | 2026-11-26 | `d7e9af6` | A unit is moved directly into an interval centred at the square root of Λ; the second unit used for comparison is no longer needed. | 57 | 5,532 |
| 29 | 2026-11-26 | `abb3397` | Bounds at the other embedding of the base field are replaced by the positivity of a coefficient of the norm. | 57 | 5,510 |
| 30 | 2026-11-26 | `bdb966f` | This positivity is derived in all five cases from the norm −2 of β. | 57 | 5,512 |
| 31 | 2026-11-26 | `4429cb1` | Auxiliary bounds are removed; the inequality 4A² ≤ Λ + 3 is used directly. | 57 | 5,507 |
| 32 | 2026-11-26 | `c5ed512` | For d = 2, the division by 11 uses only that one of two substitutions vanishes at each place modulo 11. | 57 | 5,509 |
| 33 | 2026-11-26 | `49d9ff7` | Negative signs are excluded by keeping the real values positive from the construction on, instead of by the nonnegativity of the orbit coordinates. | 56 | 5,452 |
| 34 | 2026-11-26 | `582a767` | Elements of relative norm 11 are moved directly into a small interval by powers of ρ and determined by integer arithmetic. Neither the division by 11 nor the generation of all relative units is used. | 55 | 5,049 |
| 35 | 2026-11-26 | `0f186aa` | The small elements are determined by one discriminant identity. For d = 2 the second small element is replaced by one with y = 1. | 55 | 5,033 |
