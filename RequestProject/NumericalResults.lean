import RequestProject.OpportunitySeeking
import RequestProject.KnownCorrelationAsymmetric

/-!
# Numerical constructions for Theorems 3.6, 4.3, 4.4, and 4.6

This file checks the numerical claims left open in the manuscript.  All decimals are
represented by exact rationals.
-/

namespace TrainSharing.NumericalResults

open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric

/-- The parameter box printed at the end of the proof of Theorem 3.6(3). -/
def InTheorem36OpenBox (alpha beta cost reward weight : ℝ) : Prop :=
  72 / 100 < alpha ∧ alpha < 721 / 1000 ∧
  513 / 1000 < beta ∧ beta < 514 / 1000 ∧
  755 / 1000 < cost ∧ cost < 756 / 1000 ∧
  999 / 1000 < reward ∧ reward < 1001 / 1000 ∧
  1 / 2 < weight ∧ weight < 50001 / 100000

/-- The explicit strict inequalities needed by the open-set construction.  The two
worlds have respectively independent signals (`rho = alpha*beta`) and maximally
positively correlated signals (`rho = beta`).  The clauses check feasibility, the
prescribed full-sharing actions, the relevant train/no-sharing incentive constraints,
and the paper's final primary-firm payoff comparison. -/
def Theorem36NumericalConditions (alpha beta cost reward weight : ℝ) : Prop :=
  1 / 2 < beta ∧ beta < alpha ∧ alpha < 1 ∧ 0 < cost ∧ 0 < reward ∧
  0 < weight ∧ weight < 1 ∧
  -- Full sharing acts on `Aa` and `Ab`, but not on `Ba` or `Bb`, in both worlds.
  (∀ rho ∈ ({alpha * beta, beta} : Set ℝ),
    0 < weightedSharedScore alpha beta rho reward cost true true ∧
    0 < weightedSharedScore alpha beta rho reward cost true false ∧
    weightedSharedScore alpha beta rho reward cost false true < 0 ∧
    weightedSharedScore alpha beta rho reward cost false false < 0) ∧
  -- Under train sharing: both follow at independence; only Firm 1 acts at max correlation.
  (∀ x, if follow x then 0 < weightedFirm1Gain alpha beta (alpha * beta) reward cost follow x
                       else weightedFirm1Gain alpha beta (alpha * beta) reward cost follow x < 0) ∧
  (∀ y, if follow y then 0 < weightedFirm2Gain alpha beta (alpha * beta) reward cost follow y
                       else weightedFirm2Gain alpha beta (alpha * beta) reward cost follow y < 0) ∧
  (∀ x, if follow x then 0 < weightedFirm1Gain alpha beta beta reward cost (fun _ => false) x
                       else weightedFirm1Gain alpha beta beta reward cost (fun _ => false) x < 0) ∧
  (∀ y, weightedFirm2Gain alpha beta beta reward cost follow y < 0) ∧
  -- Under no sharing, averaging the two worlds makes both firms follow.
  (∀ x, if follow x then 0 < weight * weightedFirm1Gain alpha beta (alpha * beta) reward cost follow x +
      (1 - weight) * weightedFirm1Gain alpha beta beta reward cost follow x
    else weight * weightedFirm1Gain alpha beta (alpha * beta) reward cost follow x +
      (1 - weight) * weightedFirm1Gain alpha beta beta reward cost follow x < 0) ∧
  (∀ y, if follow y then 0 < weight * weightedFirm2Gain alpha beta (alpha * beta) reward cost follow y +
      (1 - weight) * weightedFirm2Gain alpha beta beta reward cost follow y
    else weight * weightedFirm2Gain alpha beta (alpha * beta) reward cost follow y +
      (1 - weight) * weightedFirm2Gain alpha beta beta reward cost follow y < 0) ∧
  -- The displayed no-sharing payoff of Firm 1 exceeds its full-sharing payoff.
  (reward * alpha - cost * (1 - alpha)) / 4 <
    (weight * (reward * (alpha * beta / 2 + alpha * (1 - beta)) -
      cost * ((1 - alpha) * (1 - beta) / 2 + (1 - alpha) * beta)) +
     (1 - weight) * (reward * (beta / 2 + alpha - beta) - cost * ((1 - alpha) / 2))) / 2

/-- The center of the manuscript's displayed parameter box satisfies every strict
numerical condition in its construction. -/
theorem theorem3_6_open_box_center_valid :
    InTheorem36OpenBox (1441/2000) (1027/2000) (1511/2000) 1 (100001/200000) ∧
    Theorem36NumericalConditions (1441/2000) (1027/2000) (1511/2000) 1 (100001/200000) := by
  norm_num [InTheorem36OpenBox, Theorem36NumericalConditions, weightedSharedScore,
    weightedFirm1Gain, weightedFirm2Gain, conditionalMass, follow, shareFactor]

/-- Exact trade probability in the Theorem 4.3 lower-bound construction.  In the
anti-correlated world both firms follow their signals; in the maximally correlated world
only Firm 1 follows. -/
noncomputable def theorem43TrainTrade (alpha beta weight : ℝ) : ℝ :=
  weight * ((3 - alpha - beta) / 2) + (1 - weight) * (1 / 2)

/-- The manuscript's lower-bound example for Theorem 4.3(2), at its printed parameters
`α = 0.852466`, `β = 0.500087`, `w = 0.436894`, `R₁ = 1`, `C₁ = 0.647534`.  The
anti-correlated world has both firms follow their signals, while in the maximally
correlated world only Firm 1 follows.  No sharing has only Firm 1 follow.  Besides the
exact trade ratio — `≈ 1.28287`, the constant printed in the manuscript — the conjunction
checks all strict train- and no-sharing incentive conditions and the payoff comparisons
used to exclude train and full sharing from IRPO. -/
theorem theorem4_3_lower_bound_example :
    let alpha : ℝ := 852466 / 1000000
    let beta : ℝ := 500087 / 1000000
    let weight : ℝ := 436894 / 1000000
    let cost : ℝ := 647534 / 1000000
    let anti := alpha + beta - 1
    let corr := beta
    (∀ x, if follow x then 0 < weightedFirm1Gain alpha beta anti 1 cost follow x
                         else weightedFirm1Gain alpha beta anti 1 cost follow x < 0) ∧
    (∀ y, if follow y then 0 < weightedFirm2Gain alpha beta anti 1 cost follow y
                         else weightedFirm2Gain alpha beta anti 1 cost follow y < 0) ∧
    (∀ x, if follow x then 0 < weightedFirm1Gain alpha beta corr 1 cost (fun _ => false) x
                         else weightedFirm1Gain alpha beta corr 1 cost (fun _ => false) x < 0) ∧
    (∀ y, weightedFirm2Gain alpha beta corr 1 cost follow y < 0) ∧
    (∀ x, if follow x then
        0 < weight * weightedFirm1Gain alpha beta anti 1 cost (fun _ => false) x +
          (1-weight) * weightedFirm1Gain alpha beta corr 1 cost (fun _ => false) x
      else weight * weightedFirm1Gain alpha beta anti 1 cost (fun _ => false) x +
          (1-weight) * weightedFirm1Gain alpha beta corr 1 cost (fun _ => false) x < 0) ∧
    (∀ y, weight * weightedFirm2Gain alpha beta anti 1 cost follow y +
          (1-weight) * weightedFirm2Gain alpha beta corr 1 cost follow y < 0) ∧
    weight * weightedNoSharingPayoff1 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff1 alpha beta corr 1 cost follow (fun _ => false) <
      weight * weightedNoSharingPayoff1 alpha beta anti 1 cost follow (fun _ => false) +
        (1-weight) * weightedNoSharingPayoff1 alpha beta corr 1 cost follow (fun _ => false) ∧
    (weight * weightedNoSharingPayoff2 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff2 alpha beta corr 1 cost follow (fun _ => false) > 0) ∧
    conjunctionFullSharingPayoff alpha beta anti 1 cost <
      weight * weightedNoSharingPayoff1 alpha beta anti 1 cost follow (fun _ => false) +
        (1-weight) * weightedNoSharingPayoff1 alpha beta corr 1 cost follow (fun _ => false) ∧
    theorem43TrainTrade alpha beta weight = 641432854809 / 1000000000000 ∧
    theorem43TrainTrade alpha beta weight / (1/2) = 641432854809 / 500000000000 ∧
    1282865 / 1000000 < theorem43TrainTrade alpha beta weight / (1/2) ∧
    theorem43TrainTrade alpha beta weight / (1/2) < 1282866 / 1000000 := by
  norm_num [weightedFirm1Gain, weightedFirm2Gain, weightedNoSharingPayoff1,
    weightedNoSharingPayoff2, conjunctionFullSharingPayoff, theorem43TrainTrade,
    conditionalMass, follow, shareFactor]

/-- Trade probability under a two-world construction, allowing a different equilibrium
trade probability in each revealed world. -/
noncomputable def twoWorldTrade (weight first second : ℝ) : ℝ :=
  weight * first + (1 - weight) * second

/-- The manuscript's lower-bound example for Theorem 4.6(2), at its printed parameters
`α = 0.749051`, `β = 0.5`, `w = 0.0615649`, `R₁ = 1`, `C₁ = 0.715444`.  The first world is
maximally anti-correlated and the second is independent.  Train sharing uses
`follow/follow` in the first and `follow/inactive` in the second; no sharing uses
`follow/follow` in both.  The exact consumer ratio is `≈ 1.44848`, the constant printed in
the manuscript.
The theorem also verifies strict equilibrium conditions and the strict two-firm payoff
improvement that makes train sharing individually rational over no sharing. -/
theorem theorem4_6_lower_bound_example :
    let alpha : ℝ := 749051 / 1000000
    let beta : ℝ := 1 / 2
    let weight : ℝ := 615649 / 10000000
    let cost : ℝ := 715444 / 1000000
    let anti := alpha + beta - 1
    let indep := alpha * beta
    let trainTrade := twoWorldTrade weight ((3-alpha-beta)/2) (1/2)
    let noTrade := twoWorldTrade weight ((3-alpha-beta)/2) ((1+alpha+beta-2*alpha*beta)/2)
    (∀ x, if follow x then 0 < weightedFirm1Gain alpha beta anti 1 cost follow x
                         else weightedFirm1Gain alpha beta anti 1 cost follow x < 0) ∧
    (∀ y, if follow y then 0 < weightedFirm2Gain alpha beta anti 1 cost follow y
                         else weightedFirm2Gain alpha beta anti 1 cost follow y < 0) ∧
    (∀ x, if follow x then 0 < weightedFirm1Gain alpha beta indep 1 cost (fun _ => false) x
                         else weightedFirm1Gain alpha beta indep 1 cost (fun _ => false) x < 0) ∧
    (∀ y, weightedFirm2Gain alpha beta indep 1 cost follow y < 0) ∧
    (∀ x, if follow x then
        0 < weight * weightedFirm1Gain alpha beta anti 1 cost follow x +
          (1-weight) * weightedFirm1Gain alpha beta indep 1 cost follow x
      else weight * weightedFirm1Gain alpha beta anti 1 cost follow x +
          (1-weight) * weightedFirm1Gain alpha beta indep 1 cost follow x < 0) ∧
    (∀ y, if follow y then
        0 < weight * weightedFirm2Gain alpha beta anti 1 cost follow y +
          (1-weight) * weightedFirm2Gain alpha beta indep 1 cost follow y
      else weight * weightedFirm2Gain alpha beta anti 1 cost follow y +
          (1-weight) * weightedFirm2Gain alpha beta indep 1 cost follow y < 0) ∧
    weight * weightedNoSharingPayoff1 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff1 alpha beta indep 1 cost follow (fun _ => false) >
      weight * weightedNoSharingPayoff1 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff1 alpha beta indep 1 cost follow follow ∧
    weight * weightedNoSharingPayoff2 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff2 alpha beta indep 1 cost follow (fun _ => false) >
      weight * weightedNoSharingPayoff2 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff2 alpha beta indep 1 cost follow follow ∧
    weight * conjunctionFullSharingPayoff alpha beta anti 1 cost +
        (1-weight) * conjunctionFullSharingPayoff alpha beta indep 1 cost <
      weight * weightedNoSharingPayoff1 alpha beta anti 1 cost follow follow +
        (1-weight) * weightedNoSharingPayoff1 alpha beta indep 1 cost follow (fun _ => false) ∧
    noTrade = 15154496500901 / 20000000000000 ∧
    trainTrade = 10462321000901 / 20000000000000 ∧
    noTrade / trainTrade = 15154496500901 / 10462321000901 ∧
    1448483 / 1000000 < noTrade / trainTrade ∧
    noTrade / trainTrade < 1448484 / 1000000 ∧
    trainTrade < noTrade := by
  norm_num [weightedFirm1Gain, weightedFirm2Gain, weightedNoSharingPayoff1,
    weightedNoSharingPayoff2, conjunctionFullSharingPayoff, twoWorldTrade,
    conditionalMass, follow, shareFactor]

/-- Cost selected in the first construction of Theorem 4.4. -/
noncomputable def theorem44Cost (alpha beta : ℝ) : ℝ := (1 + 3 * alpha - beta) / (4 - 4 * alpha)

/-- The selected cost lies strictly between the two bounds used in Theorem 4.4. -/
theorem theorem4_4_cost_between {alpha beta : ℝ}
    (ha : alpha < 1) (hsum : 1 < alpha + beta) :
    (1 + alpha - beta) / (2 - 2 * alpha) < theorem44Cost alpha beta ∧
      theorem44Cost alpha beta < alpha / (1 - alpha) := by
  unfold theorem44Cost
  have h1 : 0 < 2 - 2 * alpha := by linarith
  have h2 : 0 < 4 - 4 * alpha := by linarith
  have h3 : 0 < 1 - alpha := by linarith
  refine ⟨?_, ?_⟩
  · field_simp
    linarith
  · field_simp
    linarith

/-- Formal unbounded approximation statement from Theorem 4.4(1).  For every positive
factor `lambda`, there are admissible accuracies and a cost satisfying the paper's strict
IRPO interval, while no sharing's trade probability is more than `lambda` times the
full-sharing probability. -/
theorem theorem4_4_arbitrarily_bad (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ alpha beta cost : ℝ,
      1 / 2 ≤ beta ∧ beta ≤ alpha ∧ alpha < 1 ∧ 1 < alpha + beta ∧
      (1 + alpha - beta) / (2 - 2 * alpha) < cost ∧ cost < alpha / (1 - alpha) ∧
      lambda * ((alpha + beta - 1) / 2) < 1 / 2 := by
  -- Set delta = min(1/8, 1/(4*lambda)) to ensure all constraints are satisfied
  let delta := min (1/8) (1/(4*lambda))
  have hdelta_pos : 0 < delta := by
    simp only [delta]
    apply lt_min (by norm_num : (1:ℝ)/8 > 0)
    exact one_div_pos.mpr (by nlinarith)
  have hdelta_lt : delta < 1/2 := by
    simp [delta]
    exact Or.inl (by norm_num)
  -- alpha = 1/2 + delta, beta = 1/2
  let alpha := 1/2 + delta
  let beta := (1:ℝ)/2
  have hab_sum : alpha + beta = 1 + delta := by
    simp [alpha, beta]
    ring
  have halpha_lt : alpha < 1 := by
    simp [alpha]
    linarith
  have hab_sum_gt : 1 < alpha + beta := by
    rw [hab_sum]
    linarith
  have hbeta_le_alpha : beta ≤ alpha := by
    simp [alpha, beta]
    linarith
  -- Need to show lower bound < upper bound for cost
  have htwo_minus_two_alpha_pos : 2 - 2 * alpha > 0 := by
    simp [alpha]
    linarith
  have halpha_lt_one' : 1 - alpha > 0 := by linarith
  -- Compute the bounds
  have hlower : (1 + alpha - beta) / (2 - 2 * alpha) = (1 + delta) / (1 - 2 * delta) := by
    simp [alpha, beta]
    field_simp
    ring
  have hupper : alpha / (1 - alpha) = (1 + 2 * delta) / (1 - 2 * delta) := by
    simp [alpha]
    field_simp
    ring
  have h1_minus_2delta_pos : 1 - 2 * delta > 0 := by linarith
  have hlow_lt_high : (1 + delta) / (1 - 2 * delta) < (1 + 2 * delta) / (1 - 2 * delta) := by
    apply div_lt_div_of_pos_right (by linarith : 1 + delta < 1 + 2 * delta) h1_minus_2delta_pos
  -- Cost = midpoint of the interval
  let cost := ((1 + delta) / (1 - 2 * delta) + (1 + 2 * delta) / (1 - 2 * delta)) / 2
  have hcost_bounds : (1 + alpha - beta) / (2 - 2 * alpha) < cost ∧ cost < alpha / (1 - alpha) := by
    simp [cost, hlower, hupper]
    constructor <;> linarith
  have hfinal : lambda * ((alpha + beta - 1) / 2) < 1 / 2 := by
    rw [hab_sum]
    have hlam_delta : lambda * delta ≤ 1/4 := by
      have := min_le_right (1/8 : ℝ) (1/(4*lambda))
      calc lambda * delta ≤ lambda * (1 / (4 * lambda)) := by nlinarith
        _ = 1 / 4 := by field_simp
    linarith
  exact ⟨alpha, beta, cost, by simp [beta], hbeta_le_alpha, halpha_lt, hab_sum_gt, hcost_bounds.1, hcost_bounds.2, hfinal⟩

/-- The concrete pro-trade example in Theorem 4.4(2): at `alpha=.7`, `beta=.6`,
`R₁=1`, `C₁=3`, inactivity is a no-sharing equilibrium, whereas full sharing acts
strictly only on `Aa`, giving each firm a positive payoff and positive trade probability. -/
theorem theorem4_4_pro_trade_example :
    (∀ x, weightedFirm1Gain (7/10) (3/5) (21/50) 1 3 (fun _ => false) x ≤ 0) ∧
    (∀ y, weightedFirm2Gain (7/10) (3/5) (21/50) 1 3 (fun _ => false) y ≤ 0) ∧
    0 < weightedSharedScore (7/10) (3/5) (21/50) 1 3 true true ∧
    weightedSharedScore (7/10) (3/5) (21/50) 1 3 true false < 0 ∧
    weightedSharedScore (7/10) (3/5) (21/50) 1 3 false true < 0 ∧
    weightedSharedScore (7/10) (3/5) (21/50) 1 3 false false < 0 ∧
    0 < conjunctionFullSharingPayoff (7/10) (3/5) (21/50) 1 3 ∧
    (0 : ℝ) < (21/50 + (1 - 7/10 - 3/5 + 21/50)) / 2 := by
  simp [weightedFirm1Gain, weightedFirm2Gain, weightedSharedScore, conjunctionFullSharingPayoff,
    conditionalMass, shareFactor]
  norm_num

end TrainSharing.NumericalResults
