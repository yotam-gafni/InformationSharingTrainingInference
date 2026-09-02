import RequestProject.KnownCorrelation

/-!
# Asymmetric known-correlation example

This file verifies the concrete construction from the asymmetric part of Lemma 3.2
(Appendix Lemma B.1): conditionally independent signals with `alpha = 0.9`,
`beta = 0.85`, reward `R₁ = 1`, and mistake cost `C₁ = 2.5`.
-/

namespace TrainSharing.Correlation.Known.Asymmetric

open TrainSharing.Correlation.Known

/-- Significant-action score with reward `reward` and mistake cost `cost`. -/
def weightedSharedScore (alpha beta rho reward cost : ℝ) (x y : Bool) : ℝ :=
  reward * conditionalMass alpha beta rho true x y -
    cost * conditionalMass alpha beta rho false x y

/-- Interim gain from action one for Firm 1 against a private-signal strategy. -/
noncomputable def weightedFirm1Gain (alpha beta rho reward cost : ℝ)
    (s2 : Bool → Bool) (x : Bool) : ℝ :=
  ∑ label : Bool, ∑ y : Bool,
    (1 / 2 : ℝ) * conditionalMass alpha beta rho label x y *
      (if label then reward else -cost) * shareFactor (s2 y)

/-- Interim gain from action one for Firm 2 against a private-signal strategy. -/
noncomputable def weightedFirm2Gain (alpha beta rho reward cost : ℝ)
    (s1 : Bool → Bool) (y : Bool) : ℝ :=
  ∑ label : Bool, ∑ x : Bool,
    (1 / 2 : ℝ) * conditionalMass alpha beta rho label x y *
      (if label then reward else -cost) * shareFactor (s1 x)

/-- Signal-by-signal equilibrium condition for asymmetric significant-action utility. -/
def IsWeightedNoSharingNash (alpha beta rho reward cost : ℝ)
    (s1 s2 : Bool → Bool) : Prop :=
  (∀ x, if s1 x then 0 ≤ weightedFirm1Gain alpha beta rho reward cost s2 x
                  else weightedFirm1Gain alpha beta rho reward cost s2 x ≤ 0) ∧
  (∀ y, if s2 y then 0 ≤ weightedFirm2Gain alpha beta rho reward cost s1 y
                  else weightedFirm2Gain alpha beta rho reward cost s1 y ≤ 0)

/-- Ex-ante payoff to Firm 1 under private-signal strategies. -/
noncomputable def weightedNoSharingPayoff1 (alpha beta rho reward cost : ℝ)
    (s1 s2 : Bool → Bool) : ℝ :=
  ∑ label : Bool, ∑ x : Bool, ∑ y : Bool,
    (1 / 2 : ℝ) * conditionalMass alpha beta rho label x y *
      (if s1 x then (if label then reward else -cost) * shareFactor (s2 y) else 0)

/-- Ex-ante payoff to Firm 2 under private-signal strategies. -/
noncomputable def weightedNoSharingPayoff2 (alpha beta rho reward cost : ℝ)
    (s1 s2 : Bool → Bool) : ℝ :=
  ∑ label : Bool, ∑ x : Bool, ∑ y : Bool,
    (1 / 2 : ℝ) * conditionalMass alpha beta rho label x y *
      (if s2 y then (if label then reward else -cost) * shareFactor (s1 x) else 0)

/-- Each firm's full-sharing payoff when both act exactly on the true/true signal pair. -/
noncomputable def conjunctionFullSharingPayoff
    (alpha beta rho reward cost : ℝ) : ℝ :=
  (reward * rho - cost * (1 - alpha - beta + rho)) / 4

/-- At the paper's concrete parameters, full sharing uniquely prescribes acting only when
both inference signals are positive.  All four signal-pair scores are strict. -/
theorem concrete_fullSharing_action_scores :
    0 < weightedSharedScore (9/10) (17/20) (153/200) 1 (5/2) true true ∧
    weightedSharedScore (9/10) (17/20) (153/200) 1 (5/2) true false < 0 ∧
    weightedSharedScore (9/10) (17/20) (153/200) 1 (5/2) false true < 0 ∧
    weightedSharedScore (9/10) (17/20) (153/200) 1 (5/2) false false < 0 := by
  simp [weightedSharedScore, conditionalMass]
  norm_num

/-- Both firms following their own signals is a no-sharing equilibrium at the concrete
parameters used in Appendix Lemma B.1. -/
theorem concrete_noSharing_equilibrium :
    IsWeightedNoSharingNash (9/10) (17/20) (153/200) 1 (5/2) follow follow := by
  simp [IsWeightedNoSharingNash, weightedFirm1Gain, weightedFirm2Gain, follow,
    conditionalMass, shareFactor]
  norm_num

/-- Full sharing strictly improves both firms' payoffs over that no-sharing equilibrium. -/
theorem concrete_fullSharing_strictly_better :
    weightedNoSharingPayoff1 (9/10) (17/20) (153/200) 1 (5/2) follow follow <
      conjunctionFullSharingPayoff (9/10) (17/20) (153/200) 1 (5/2) ∧
    weightedNoSharingPayoff2 (9/10) (17/20) (153/200) 1 (5/2) follow follow <
      conjunctionFullSharingPayoff (9/10) (17/20) (153/200) 1 (5/2) := by
  simp [weightedNoSharingPayoff1, weightedNoSharingPayoff2, conjunctionFullSharingPayoff,
    follow, conditionalMass, shareFactor]
  norm_num

/-! ## The paper's parametric inequalities

The following predicate records, without hiding any economic content, the inequalities
used in Appendix Lemma B.1.  We normalize `R₁ = 1` and impose independence by setting
`rho = alpha * beta`.  The first four inequalities say that under full sharing only the
joint-positive signal has positive score.  The next four are precisely the private-signal
incentive constraints for both firms to follow their signals.  The final two say that each
firm's resulting no-sharing payoff is strictly below its full-sharing payoff.
-/

/-- Explicit Appendix B.1 inequalities for a fixed `beta`. -/
def SatisfiesLemmaB1Inequalities (alpha beta cost : ℝ) : Prop :=
  0 < alpha * beta - cost * (1 - alpha) * (1 - beta) ∧
  alpha * (1 - beta) - cost * (1 - alpha) * beta < 0 ∧
  (1 - alpha) * beta - cost * alpha * (1 - beta) < 0 ∧
  (1 - alpha) * (1 - beta) - cost * alpha * beta < 0 ∧
  0 ≤ (2 * alpha - alpha * beta) - cost * (1 - alpha + beta - alpha * beta) ∧
  (2 - 2 * alpha - beta + alpha * beta) - cost * (alpha + alpha * beta) ≤ 0 ∧
  0 ≤ (2 * beta - alpha * beta) - cost * (1 + alpha - beta - alpha * beta) ∧
  (2 - alpha - 2 * beta + alpha * beta) - cost * (beta + alpha * beta) ≤ 0 ∧
  ((2 * alpha - alpha * beta) - cost * (1 - alpha + beta - alpha * beta)) / 4 <
    (alpha * beta - cost * (1 - alpha) * (1 - beta)) / 4 ∧
  ((2 * beta - alpha * beta) - cost * (1 + alpha - beta - alpha * beta)) / 4 <
    (alpha * beta - cost * (1 - alpha) * (1 - beta)) / 4

/-- The paper's displayed numerical example satisfies all ten inequalities exactly. -/
theorem concrete_satisfies_lemmaB1_inequalities :
    SatisfiesLemmaB1Inequalities (9 / 10) (17 / 20) (5 / 2) := by
  norm_num [SatisfiesLemmaB1Inequalities]

/-- The first four explicit inequalities are exactly the strict full-sharing action
conditions. -/
theorem lemmaB1_inequalities_fullSharing (alpha beta cost : ℝ)
    (h : SatisfiesLemmaB1Inequalities alpha beta cost) :
    0 < weightedSharedScore alpha beta (alpha * beta) 1 cost true true ∧
    weightedSharedScore alpha beta (alpha * beta) 1 cost true false < 0 ∧
    weightedSharedScore alpha beta (alpha * beta) 1 cost false true < 0 ∧
    weightedSharedScore alpha beta (alpha * beta) 1 cost false false < 0 := by
  simp [weightedSharedScore, conditionalMass]
  have h1 := h.1
  have h2 := h.2.1
  have h3 := h.2.2.1
  have h4 := h.2.2.2.1
  ring_nf
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The middle four inequalities guarantee the no-sharing behavior used in Lemma B.1:
both firms follow their private inference signals. -/
theorem lemmaB1_inequalities_noSharing (alpha beta cost : ℝ)
    (h : SatisfiesLemmaB1Inequalities alpha beta cost) :
    IsWeightedNoSharingNash alpha beta (alpha * beta) 1 cost follow follow := by
  unfold IsWeightedNoSharingNash
  simp [weightedFirm1Gain, weightedFirm2Gain, follow, conditionalMass, shareFactor]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring_nf <;> linarith [h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1]

/-- The last two inequalities guarantee that both firms strictly prefer full sharing to
the specified no-sharing equilibrium. -/
theorem lemmaB1_inequalities_payoffs (alpha beta cost : ℝ)
    (h : SatisfiesLemmaB1Inequalities alpha beta cost) :
    weightedNoSharingPayoff1 alpha beta (alpha * beta) 1 cost follow follow <
      conjunctionFullSharingPayoff alpha beta (alpha * beta) 1 cost ∧
    weightedNoSharingPayoff2 alpha beta (alpha * beta) 1 cost follow follow <
      conjunctionFullSharingPayoff alpha beta (alpha * beta) 1 cost := by
  simp [weightedNoSharingPayoff1, weightedNoSharingPayoff2, conjunctionFullSharingPayoff,
    follow, conditionalMass, shareFactor]
  ring_nf
  have h1 := h.2.2.2.2.2.2.2.2.1
  have h2 := h.2.2.2.2.2.2.2.2.2
  ring_nf at h1 h2
  exact ⟨h1, h2⟩

/-- The paper's rational reduction supplies parameters satisfying all Appendix B.1
inequalities for every nondegenerate accuracy `beta`.  The endpoint restrictions are
necessary: at `beta = 1/2` strict improvement is unavailable, while the displayed cost
has a pole at `beta = 1`. -/
theorem lemmaB1_parameter_reduction (beta : ℝ) (hhalf : 1 / 2 < beta) (hone : beta < 1) :
    SatisfiesLemmaB1Inequalities beta beta
      ((2 * beta ^ 2 - 2 * beta - 1) / (2 * (beta - 1) * (beta + 1))) := by
  unfold SatisfiesLemmaB1Inequalities
  set denom := 2 * (beta - 1) * (beta + 1) with hdenom_def
  set cost := (2 * beta ^ 2 - 2 * beta - 1) / denom with hcost_def
  have hdenom_neg : denom < 0 := by nlinarith
  have hdenom_ne : denom ≠ 0 := by linarith
  simp only [hcost_def]
  have h1 : 0 < beta * beta - cost * (1 - beta) * (1 - beta) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [sub_div', lt_div_iff_of_neg hdenom_neg]
    · ring_nf
      nlinarith [sq_nonneg (beta - 1/2), sq_nonneg (beta - 1), sq_nonneg (beta + 1), sq_nonneg (1 - beta)]
    · exact hdenom_ne
  have h2beta_neg : 1 - 2 * beta < 0 := by linarith
  have h1beta_pos : 1 - beta > 0 := by linarith
  have hbeta_pos : beta > 0 := by linarith
  have h2 : beta * (1 - beta) < cost * (1 - beta) * beta := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [lt_div_iff_of_neg hdenom_neg]
    simp only [hdenom_def]
    ring_nf
    nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
  have h3 : (1 - beta) * beta < cost * beta * (1 - beta) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [lt_div_iff_of_neg hdenom_neg]
    simp only [hdenom_def]
    ring_nf
    nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
  have h4 : (1 - beta) * (1 - beta) < cost * beta * beta := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [lt_div_iff_of_neg hdenom_neg]
    simp only [hdenom_def]
    ring_nf
    nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
  have h5 : 0 ≤ 2 * beta - beta * beta - cost * (1 - beta + beta - beta * beta) := by
    rw [div_mul_eq_mul_div]
    rw [sub_div']
    rw [le_div_iff_of_neg hdenom_neg]
    · simp only [hdenom_def]
      ring_nf
      nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
    · exact hdenom_ne
  have h6 : 2 - 2 * beta - beta + beta * beta - cost * (beta + beta * beta) ≤ 0 := by
    rw [div_mul_eq_mul_div]
    rw [sub_div']
    rw [div_le_iff_of_neg hdenom_neg]
    · simp only [hdenom_def]
      ring_nf
      nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
    · exact hdenom_ne
  have h7 : 0 ≤ 2 * beta - beta * beta - cost * (1 + beta - beta - beta * beta) := by
    rw [div_mul_eq_mul_div]
    rw [sub_div']
    rw [le_div_iff_of_neg hdenom_neg]
    · simp only [hdenom_def]
      ring_nf
      nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
    · exact hdenom_ne
  have h8 : 2 - beta - 2 * beta + beta * beta - cost * (beta + beta * beta) ≤ 0 := by
    rw [div_mul_eq_mul_div]
    rw [sub_div']
    rw [div_le_iff_of_neg hdenom_neg]
    · simp only [hdenom_def]
      ring_nf
      nlinarith [mul_pos hbeta_pos (mul_pos h1beta_pos (sub_pos.mpr h2beta_neg))]
    · exact hdenom_ne
  have hcost_gt_1 : cost > 1 := by
    rw [gt_iff_lt, hcost_def]
    rw [lt_div_iff_of_neg hdenom_neg]
    simp only [hdenom_def]
    nlinarith [sq_nonneg (beta - 1), sq_nonneg (beta - 1/2)]
  have h9 : (2 * beta - beta * beta - cost * (1 - beta + beta - beta * beta)) / 4 <
            (beta * beta - cost * (1 - beta) * (1 - beta)) / 4 := by
    rw [div_lt_div_iff_of_pos_right (by norm_num : (4 : ℝ) > (0 : ℝ))]
    ring_nf
    have : 2 * beta * (1 - beta) * (1 - cost) < 0 := mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hbeta_pos) h1beta_pos) (sub_neg.mpr hcost_gt_1)
    linarith
  have h10 : (2 * beta - beta * beta - cost * (1 + beta - beta - beta * beta)) / 4 <
             (beta * beta - cost * (1 - beta) * (1 - beta)) / 4 := by
    rw [div_lt_div_iff_of_pos_right (by norm_num : (4 : ℝ) > (0 : ℝ))]
    ring_nf
    have : 2 * beta * (1 - beta) * (1 - cost) < 0 := mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hbeta_pos) h1beta_pos) (sub_neg.mpr hcost_gt_1)
    linarith
  refine ⟨h1, ?_, ?_, ?_, h5, h6, h7, h8, h9, h10⟩
  all_goals simp_all

/-- Parametric asymmetric case of Lemma 3.2/B.1: for any fixed `beta`, once `alpha` and
`cost` satisfy the paper's inequalities, the claimed full-sharing action rule,
no-sharing equilibrium behavior, and strict two-firm payoff improvement all follow. -/
theorem lemma3_2_asymmetric_of_inequalities (beta alpha cost : ℝ)
    (h : SatisfiesLemmaB1Inequalities alpha beta cost) :
    (0 < weightedSharedScore alpha beta (alpha * beta) 1 cost true true ∧
      weightedSharedScore alpha beta (alpha * beta) 1 cost true false < 0 ∧
      weightedSharedScore alpha beta (alpha * beta) 1 cost false true < 0 ∧
      weightedSharedScore alpha beta (alpha * beta) 1 cost false false < 0) ∧
    IsWeightedNoSharingNash alpha beta (alpha * beta) 1 cost follow follow ∧
    (weightedNoSharingPayoff1 alpha beta (alpha * beta) 1 cost follow follow <
        conjunctionFullSharingPayoff alpha beta (alpha * beta) 1 cost ∧
      weightedNoSharingPayoff2 alpha beta (alpha * beta) 1 cost follow follow <
        conjunctionFullSharingPayoff alpha beta (alpha * beta) 1 cost) := by
  exact ⟨lemmaB1_inequalities_fullSharing alpha beta cost h,
    lemmaB1_inequalities_noSharing alpha beta cost h,
    lemmaB1_inequalities_payoffs alpha beta cost h⟩

/-- The reduced mistake cost is strictly positive on the admissible interval, so it
defines a valid nonnegative utility parameter. -/
theorem lemmaB1_reduced_cost_positive (beta : ℝ) (hhalf : 1 / 2 < beta) (hone : beta < 1) :
    0 < (2 * beta ^ 2 - 2 * beta - 1) / (2 * (beta - 1) * (beta + 1)) := by
  apply div_pos_of_neg_of_neg
  · nlinarith [sq_nonneg (beta - 1 / 2)]
  · exact mul_neg_of_neg_of_pos (by nlinarith) (by linarith)

/-- Fully existential asymmetric clause of Lemma 3.2/B.1.  For every interior
`beta`, explicit `alpha` and cost parameters produce the full-sharing action rule,
the no-sharing equilibrium, and strict Pareto improvement claimed in the paper. -/
theorem lemma3_2_asymmetric_exists (beta : ℝ) (hhalf : 1 / 2 < beta) (hone : beta < 1) :
    ∃ alpha cost,
      (0 < weightedSharedScore alpha beta (alpha * beta) 1 cost true true ∧
        weightedSharedScore alpha beta (alpha * beta) 1 cost true false < 0 ∧
        weightedSharedScore alpha beta (alpha * beta) 1 cost false true < 0 ∧
        weightedSharedScore alpha beta (alpha * beta) 1 cost false false < 0) ∧
      IsWeightedNoSharingNash alpha beta (alpha * beta) 1 cost follow follow ∧
      (weightedNoSharingPayoff1 alpha beta (alpha * beta) 1 cost follow follow <
          conjunctionFullSharingPayoff alpha beta (alpha * beta) 1 cost ∧
        weightedNoSharingPayoff2 alpha beta (alpha * beta) 1 cost follow follow <
          conjunctionFullSharingPayoff alpha beta (alpha * beta) 1 cost) := by
  let cost := (2 * beta ^ 2 - 2 * beta - 1) / (2 * (beta - 1) * (beta + 1))
  exact ⟨beta, cost,
    lemma3_2_asymmetric_of_inequalities beta beta cost
      (lemmaB1_parameter_reduction beta hhalf hone)⟩


end TrainSharing.Correlation.Known.Asymmetric
