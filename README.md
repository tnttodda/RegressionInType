# Global Optimisation with Constructive Reals

This development formalises the proofs seen in our paper submission. We go through each numbered Definition/Lemma/Theorem/Corollary from the paper in order, and give which type or function formalises that statement in the code. The key results (Theorems in the paper) are numbered in **bold** for easy recognition.

Recall that this development is built on top of Martín Escardó's library [TypeTopology](https://github.com/martinescardo/TypeTopology), and utilises many of its files.

-----

**Section II-B** is formalised in the file `Codistances.agda` 

| #  | Formalisation                        
|----|-
| 01 | In `TypeTopology` file `Codistance.lagda` as `is-codistance`
| 02 | Not formalised in this repo
| 03 | Not formalised in this repo
| 04 | `×-codistance` and `×ⁿ-codistance`
| 05 | Not formalised in this repo
| 06 | In `TypeTopology` file `Codistance.lagda` as `codistance`
| 07 | In `TypeTopology` file `Codistance.lagda` as `ℕ→D-has-codistance`
| 08 | In `TypeTopology` file `Codistance.lagda` as `ℕ∞-has-codistance`
| 09 | `≈→≼` and `≼→≈`
| 10 | `continuous²`
| 11 | `continuous`
| 12 | `→-everywhere-sin` and `→-right-continuous`
| 13 | `×ⁿ-everywhere-sin` and `×ⁿ-right-continuous`

**Section II-C** is formalised in the file `SearchableTypes.agda` 

| #  | Formalisation                        
|----|-
| 14 | `searchable`
| 15 | `c-searchable`
| 16 | `searchable→c-searchable` 
| 17 | Not formalised in this repo
| **18** | `→-c-searchable`
| **19** | `×-c-searchable`

**Section III-A** is formalised in the files `ESIntervalObject.lagda` and `IntervalObjectApproximation.agda`. The following formalisations are all in the latter.

| #  | Formalisation
|----|-
| 20 | `n-approx`
| 21 | `approximation` and `approx-holds`
| 22 | `fg-approx-holds`

**Section III-B** is formalised in the files [i] `SignedDigit.agda`, [ii] `SignedDigitContinuity.agda` and [iii] `SignedDigitIntervalObject.agda`.

| #  | File | Formalisation
|----|------|---
| 23 | [ii] | `c3^N` and `c3^N-coultrametric`
| 24 | [ii] | `≈-continuous→≼-continuous`
| 25 | [ii] | `map-continuous`
| 26 | [ii] | `map2-continuous`
| 27 | [iii]| `map-realiser`
| 28 | [ii] | `neg-continuous≼`
| 29 | [iii]| `neg-realiser`
| 30 | [iii]| `div2-aux-≡`
| 31 | [i]  | `div2`
| 32 | [i]  | `mid`
| 33 | [ii] | `mid-continuous≼`
| 34 | [iii]| `div2-realiser`
| 35 | [iii]| `half-add-realiser`
| **36** | [iii]| `mid-realiser`
| 37 | [i]  | `bigMid`
| 38 | [ii] | `bigMid-continuous`
| 39 | [iii]| `M-bigMid'-≡`
| **40** | [iii]| `bigMid-realiser`
| 41 | [i]  | `mul`
| 42 | [ii] | `mul-continuous≼`
| 43 | [iii]| `digitMul-realiser`
| **44** | [iii] | `mul-realiser`

**Section IV** is formalised in the file `ConvergenceTheorems.agda`

| #  | Formalisation
|----|-
| 45 | `≼-decidable` and `≼-continuous`
| 46 | Within `p-regressor`
| 47 | `p-regressor`
| 48 | `≼ⁿ`
| 49 | `f-max-≼ⁿ`
| **50** | `f-minimisation`
| **51** | `minimisation-convergence`
| **52** | `perfect-convergence`
| **53** | `s-imperfect-convergence`
| **54** | `w-imperfect-convergence`
| 55 | `sampled-loss-function`
| 56 | `sampled-loss-everywhere-sin` and `sampled-loss-right-continuous`
| 57 | `c-interpolation`
| 58 | `interpolated-slf-minimises-loss`
| **59** | `interpolation-convergence`