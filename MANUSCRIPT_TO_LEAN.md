# Manuscript to Lean Formalization Mapping

This document maps the theorems and lemmas from the manuscript "Information-Sharing in Training and Inference: Collusion vs. Accuracy" to their corresponding Lean 4 formalizations.

## Section 2: General Model
* **Theorem 2.1 (Congestion Game Reduction):** `CongestionGame.lean` (`theorem2_1_congestion_reduction`, plus explicit specializations for all four contracts).

## Section 3: Correlation Model
* **Lemma 3.1 (Correlation determines joint distribution):** `CorrelationModel.lean` (`correlation_determines_joint`).
* **Lemma 3.2 (Known correlation equilibria):** 
    * Symmetric case & Regimes: `KnownCorrelation.lean` (`highBeta_equilibrium`, `lowBeta_equilibrium`, `boundary_two_equilibria`).
    * Asymmetric case: `KnownCorrelationAsymmetric.lean` (`lemma3_2_asymmetric_of_inequalities`, `lemma3_2_asymmetric_exists`).
* **Theorem 3.4 (Congestion Game in Correlation Model):** `CongestionGame.lean` (`theorem3_4_congestion_reduction`).
* **Lemma 3.5 (Full-sharing weakly dominates Infer-sharing):** `UnknownCorrelation.lean` (`lemma3_5_correlation_full_ge_infer`).
* **Theorem 3.6 (IRPO Classifications):** 
    * Parts 1 & 2: `Theorem36.lean` (`theorem3_6_part1_unique_up_to_equivalence`, `theorem3_6_part2_dichotomy`).
    * Part 3 (Open parameter subset): `Theorem36.lean` (`theorem3_6_part3_unique_train`) and `NumericalResults.lean` (`theorem3_6_open_box_center_valid`).

## Section 4: Consumer Effects
* **Theorem 4.1 (Aligned Consumer):** `Consumer.lean` (`theorem4_1_part1_aligned_prefers_ir_improvement`, `theorem4_1_part2_aligned_prefers_full_sharing`).
* **Lemma 4.2 (Opportunity-Seeking Equivalence):** `OpportunitySeeking.lean` (`lemma4_2_maximization_equiv`, `lemma4_2_normalized`).
* **Theorem 4.3 (No-sharing consumer trade):** `Theorem43.lean` (generic factor-two argument) and `Theorem43Selected.lean` (fixed equilibrium selection). The manuscript's numerical example, whose trade ratio exceeds `1.28287`, is `NumericalResults.lean` (`theorem4_3_lower_bound_example`).
* **Theorem 4.4 (Full-sharing bounds):** `NumericalResults.lean` (`theorem4_4_arbitrarily_bad`, `theorem4_4_pro_trade_example`).
* **Definition 4.5 (Inverted equilibrium):** `Theorem46Selected.lean` (`Inverted`, its pointwise negation `NonInverted`, and `nonInverted_iff_not_inverted`).
* **Theorem 4.6 (Train-sharing consumer trade):**
    * Core infrastructure: `Theorem46.lean`, `Theorem46Selected.lean`.
    * Part 2 (Upper bound without activity premise): `Theorem46UpperBound.lean` (`theorem4_6_factor_two_from_model`), with the manuscript's numerical example (trade ratio above `1.44848`) in `NumericalResults.lean` (`theorem4_6_lower_bound_example`).
    * Classification of the strict equilibria of the weighted game: `Theorem46Part1Classification.lean` (`strict_equilibrium_classification`).
    * Transfer of the trade probability from the correlation worlds to the prior mixture: `Theorem46Part1Transfer.lean` (`tradeProbability_transfer_of_monotone_worlds`).
    * Part 1 under the strong monotone-worlds condition: `Theorem46Parts.lean` (`part1_transfer_of_monotone_worlds`); Part 2 in the same file (`theorem4_6_part2`).
    * Part 1 under Definition 4.5 (the manuscript's hypothesis): `Theorem46Part1NonInverted.lean` (`theorem4_6_part1_nonInverted`, `theorem4_6_part1_existence_nonInverted`, and the dichotomy `theorem4_6_part1_or_inverted`).
    * The all-acting worlds, which the selected reading of Part 1 has to exclude: `Theorem46Part1AllActing.lean` (`theorem4_6_part1_allActing_selected_fails`, `aa_existence_conclusion_holds`).
* **Example 4.7 (Inverted equilibrium):** `Example47.lean` (`example4_7_consumer_prefers_trainSharing`, `example4_7_refutes_part1`, `nonInverted_hypothesis_is_necessary`). The instance is inverted in the sense of Definition 4.5, and the consumer's train-sharing trade probability `209/240 ≈ 0.871` exceeds the no-sharing one, `283/400 = 0.7075`; it therefore shows that the non-inversion hypothesis of Theorem 4.6(1) cannot be dropped.

## Section 5: Extensions
* **Theorem 5.1 (Two Hypotheses / Infer-sharing optimal):** `TwoHypotheses.lean` (`theorem5_1`, `theorem51Witness_region`). The proof connecting this to the general framework is in `ModelConnections.lean`.
* **Theorem 5.2 (One Sample Model):** `Theorem52.lean` (`theorem5_2`).

## General model to particular models specifications 
`GeneralSignaling.lean`, `ModelConnections.lean` 