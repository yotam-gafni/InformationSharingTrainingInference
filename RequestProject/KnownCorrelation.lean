import RequestProject.CorrelationModel

/-!
# Known-correlation results

This file isolates the finite, pure-strategy calculation behind Lemma 3.2.  We use the
paper's standing assumptions: balanced labels, symmetric false-positive/false-negative
rates, `alpha ≥ beta ≥ 1/2`, and normalized symmetric significant-action utility
`R₁ = C₁ = 1`.  `rho` is the true/true conditional cell; all incentive expressions below
are independent of it.

At the boundary `3 * beta = alpha + 1`, Firm 2 is indifferent after its positive signal.
The revised manuscript explicitly selects the yielding equilibrium there because that is
the representative relevant to IRPO; this file records both equilibrium representatives.
-/

namespace TrainSharing.Correlation.Known

/-- Conditional signal mass.  Under label `false`, both signals are complemented, as in
Equation (7). -/
def conditionalMass (alpha beta rho : ℝ) (label x y : Bool) : ℝ :=
  if label then
    if x then (if y then rho else alpha - rho)
    else (if y then beta - rho else 1 - alpha - beta + rho)
  else
    if x then (if y then 1 - alpha - beta + rho else beta - rho)
    else (if y then alpha - rho else rho)

/-- Difference between the conditional masses under labels one and zero.  With balanced
labels, this has the same sign as the posterior payoff from taking action one. -/
def sharedScore (alpha beta rho : ℝ) (x y : Bool) : ℝ :=
  conditionalMass alpha beta rho true x y - conditionalMass alpha beta rho false x y

lemma sharedScore_tt (alpha beta rho : ℝ) :
    sharedScore alpha beta rho true true = alpha + beta - 1 := by
  simp [sharedScore, conditionalMass]
  ring
lemma sharedScore_tf (alpha beta rho : ℝ) :
    sharedScore alpha beta rho true false = alpha - beta := by
  simp [sharedScore, conditionalMass]
lemma sharedScore_ft (alpha beta rho : ℝ) :
    sharedScore alpha beta rho false true = beta - alpha := by
  simp [sharedScore, conditionalMass]
lemma sharedScore_ff (alpha beta rho : ℝ) :
    sharedScore alpha beta rho false false = 1 - alpha - beta := by
  simp [sharedScore, conditionalMass]

/-- Under strict accuracy ordering, the unique full-information optimal action is exactly
Firm 1's signal. -/
theorem fullSharing_unique_action
    (alpha beta rho : ℝ) (hbeta : 1 / 2 < beta) (horder : beta < alpha) (x y : Bool) :
    (0 < sharedScore alpha beta rho x y ↔ x = true) := by
  cases x <;> cases y <;>
    simp_all [sharedScore_tt, sharedScore_tf, sharedScore_ft, sharedScore_ff] <;> linarith

/-- Market-share multiplier for action one: one if the rival stays out and one half if it
also acts. -/
noncomputable def shareFactor (rivalAction : Bool) : ℝ := if rivalAction then 1 / 2 else 1

def labelSign (label : Bool) : ℝ := if label then 1 else -1

/-- Unnormalized interim payoff from action one for Firm 2 after signal `y`, against a
strategy of Firm 1.  The omitted probability of `y` is positive under the model's
interior-accuracy assumptions, so it does not affect best responses. -/
noncomputable def firm2Gain (alpha beta rho : ℝ) (s1 : Bool → Bool) (y : Bool) : ℝ :=
  ∑ label : Bool, ∑ x : Bool,
    (1 / 2 : ℝ) * conditionalMass alpha beta rho label x y *
      labelSign label * shareFactor (s1 x)

/-- The analogous unnormalized interim payoff from action one for Firm 1. -/
noncomputable def firm1Gain (alpha beta rho : ℝ) (s2 : Bool → Bool) (x : Bool) : ℝ :=
  ∑ label : Bool, ∑ y : Bool,
    (1 / 2 : ℝ) * conditionalMass alpha beta rho label x y *
      labelSign label * shareFactor (s2 y)

/-- Follow one's own inference signal. -/
def follow : Bool → Bool := id
/-- Always take the safe action zero. -/
def inactive : Bool → Bool := fun _ => false

lemma firm2Gain_follow_true (alpha beta rho : ℝ) :
    firm2Gain alpha beta rho follow true = (3 * beta - alpha - 1) / 4 := by
  simp [firm2Gain, conditionalMass, follow, labelSign, shareFactor]
  ring
lemma firm2Gain_follow_false (alpha beta rho : ℝ) :
    firm2Gain alpha beta rho follow false = (2 - alpha - 3 * beta) / 4 := by
  simp [firm2Gain, conditionalMass, follow, labelSign, shareFactor]
  ring
lemma firm1Gain_follow_true (alpha beta rho : ℝ) :
    firm1Gain alpha beta rho follow true = (3 * alpha - beta - 1) / 4 := by
  simp [firm1Gain, conditionalMass, follow, labelSign, shareFactor]
  ring
lemma firm1Gain_follow_false (alpha beta rho : ℝ) :
    firm1Gain alpha beta rho follow false = (2 - beta - 3 * alpha) / 4 := by
  simp [firm1Gain, conditionalMass, follow, labelSign, shareFactor]
  ring
lemma firm1Gain_inactive_true (alpha beta rho : ℝ) :
    firm1Gain alpha beta rho inactive true = (2 * alpha - 1) / 2 := by
  simp [firm1Gain, conditionalMass, inactive, labelSign, shareFactor]
  ring
lemma firm1Gain_inactive_false (alpha beta rho : ℝ) :
    firm1Gain alpha beta rho inactive false = (1 - 2 * alpha) / 2 := by
  simp [firm1Gain, conditionalMass, inactive, labelSign, shareFactor]
  ring

/-- Signal-by-signal pure Nash condition.  It is equivalent to the ordinary pure Nash
condition here because a strategy's choices at the two private signals enter expected
utility independently. -/
def IsNoSharingNash (alpha beta rho : ℝ) (s1 s2 : Bool → Bool) : Prop :=
  (∀ x, if s1 x then 0 ≤ firm1Gain alpha beta rho s2 x
                  else firm1Gain alpha beta rho s2 x ≤ 0) ∧
  (∀ y, if s2 y then 0 ≤ firm2Gain alpha beta rho s1 y
                  else firm2Gain alpha beta rho s1 y ≤ 0)

/-- Strict signal-by-signal equilibrium: each prescribed action is the unique best response
at every private signal. -/
def IsStrictNoSharingNash (alpha beta rho : ℝ) (s1 s2 : Bool → Bool) : Prop :=
  (∀ x, if s1 x then 0 < firm1Gain alpha beta rho s2 x
                  else firm1Gain alpha beta rho s2 x < 0) ∧
  (∀ y, if s2 y then 0 < firm2Gain alpha beta rho s1 y
                  else firm2Gain alpha beta rho s1 y < 0)

/-- High-beta regime from Lemma 3.2: both firms follow their signals. -/
theorem highBeta_equilibrium (alpha beta rho : ℝ)
    (hhalf : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hregime : alpha + 1 ≤ 3 * beta) :
    IsNoSharingNash alpha beta rho follow follow := by
  unfold IsNoSharingNash
  have h1 : 0 ≤ (3 * alpha - beta - 1) / 4 := by linarith
  have h2 : (2 - beta - 3 * alpha) / 4 ≤ 0 := by linarith
  have h3 : 0 ≤ (3 * beta - alpha - 1) / 4 := by linarith
  have h4 : (2 - alpha - 3 * beta) / 4 ≤ 0 := by linarith
  constructor
  · intro x
    cases x with
    | true => rw [firm1Gain_follow_true]; exact h1
    | false => rw [firm1Gain_follow_false]; exact h2
  · intro y
    cases y with
    | true => rw [firm2Gain_follow_true]; exact h3
    | false => rw [firm2Gain_follow_false]; exact h4

/-- Away from the threshold and accuracy ties, the high-beta profile is strict. -/
theorem highBeta_strict_equilibrium (alpha beta rho : ℝ)
    (horder : beta < alpha) (hregime : alpha + 1 < 3 * beta) :
    IsStrictNoSharingNash alpha beta rho follow follow := by
  constructor
  · intro x
    cases x with
    | true =>
      change 0 < firm1Gain alpha beta rho follow true
      rw [firm1Gain_follow_true]
      linarith
    | false =>
      change firm1Gain alpha beta rho follow false < 0
      rw [firm1Gain_follow_false]
      linarith
  · intro y
    cases y with
    | true =>
      change 0 < firm2Gain alpha beta rho follow true
      rw [firm2Gain_follow_true]
      linarith
    | false =>
      change firm2Gain alpha beta rho follow false < 0
      rw [firm2Gain_follow_false]
      linarith

/-- Low-beta regime from Lemma 3.2: Firm 1 follows its signal and Firm 2 stays out. -/
theorem lowBeta_equilibrium (alpha beta rho : ℝ)
    (hhalf : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hregime : 3 * beta ≤ alpha + 1) :
    IsNoSharingNash alpha beta rho follow inactive := by
  constructor
  · intro x
    split_ifs with hx
    · simp [follow] at hx
      rw [hx, firm1Gain_inactive_true]
      linarith
    · simp [follow] at hx
      rw [show x = false by tauto, firm1Gain_inactive_false]
      linarith
  · intro y
    simp only [inactive]
    cases y <;> simp_all [firm2Gain_follow_true, firm2Gain_follow_false] <;> linarith

/-- Away from the threshold, the low-beta profile is strict. -/
theorem lowBeta_strict_equilibrium (alpha beta rho : ℝ)
    (hhalf : 1 / 2 < beta)
    (hregime : 3 * beta < alpha + 1) :
    IsStrictNoSharingNash alpha beta rho follow inactive := by
  constructor
  · intro x
    cases x <;> simp [follow, firm1Gain_inactive_true, firm1Gain_inactive_false] <;> linarith
  · intro y
    cases y <;> simp [inactive, firm2Gain_follow_true, firm2Gain_follow_false] <;> linarith

/-- Firm 1's ex-ante equilibrium payoff under full sharing in the symmetric model
(the two firms select the same action and split the market). -/
noncomputable def fullSharingFirm1Payoff (alpha : ℝ) : ℝ := (2 * alpha - 1) / 4

/-- Firm 1's no-sharing payoff in the high-beta regime, where both follow their signals. -/
noncomputable def highBetaFirm1Payoff (alpha beta : ℝ) : ℝ := (3 * alpha - beta - 1) / 4

/-- Firm 1's no-sharing payoff in the low-beta regime, where Firm 2 stays inactive. -/
noncomputable def lowBetaFirm1Payoff (alpha : ℝ) : ℝ := (2 * alpha - 1) / 2

/-- In the high-beta regime, Firm 1 weakly prefers no sharing to full sharing.  The gap is
`(alpha - beta)/4`, matching Equation (13) and the subsequent calculation in the paper. -/
theorem highBeta_primary_prefers_noSharing (alpha beta : ℝ) (horder : beta ≤ alpha) :
    fullSharingFirm1Payoff alpha ≤ highBetaFirm1Payoff alpha beta := by
  unfold fullSharingFirm1Payoff highBetaFirm1Payoff
  linarith

/-- In the low-beta regime, an accurate Firm 1 weakly prefers no sharing to full sharing;
with `alpha > 1/2` the preference is strict. -/
theorem lowBeta_primary_prefers_noSharing (alpha : ℝ) (hhalf : 1 / 2 ≤ alpha) :
    fullSharingFirm1Payoff alpha ≤ lowBetaFirm1Payoff alpha := by
  unfold fullSharingFirm1Payoff lowBetaFirm1Payoff
  linarith

theorem lowBeta_primary_strictly_prefers_noSharing (alpha : ℝ) (hhalf : 1 / 2 < alpha) :
    fullSharingFirm1Payoff alpha < lowBetaFirm1Payoff alpha := by
  unfold fullSharingFirm1Payoff lowBetaFirm1Payoff
  linarith

/-- At the regime boundary, both profiles are equilibria.  This is the indifference case
explicitly discussed in the revised manuscript, which selects yielding for the IRPO
comparison. -/
theorem boundary_two_equilibria (alpha beta rho : ℝ)
    (hhalf : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hboundary : 3 * beta = alpha + 1) :
    IsNoSharingNash alpha beta rho follow follow ∧
      IsNoSharingNash alpha beta rho follow inactive := by
  constructor
  · -- follow follow is a Nash equilibrium
    constructor
    · -- Firm 1's incentive constraints
      intro x
      cases x with
      | true =>
        rw [firm1Gain_follow_true]
        simp [follow]
        linarith
      | false =>
        rw [firm1Gain_follow_false]
        simp [follow]
        linarith
    · -- Firm 2's incentive constraints
      intro y
      cases y with
      | true =>
        rw [firm2Gain_follow_true]
        simp [follow]
        linarith
      | false =>
        rw [firm2Gain_follow_false]
        simp [follow]
        linarith
  · -- follow inactive is a Nash equilibrium
    constructor
    · -- Firm 1's incentive constraints
      intro x
      cases x with
      | true =>
        rw [firm1Gain_inactive_true]
        simp [follow]
        linarith
      | false =>
        rw [firm1Gain_inactive_false]
        simp [follow]
        linarith
    · -- Firm 2's incentive constraints
      intro y
      cases y with
      | true =>
        rw [firm2Gain_follow_true]
        simp [inactive]
        linarith
      | false =>
        rw [firm2Gain_follow_false]
        simp [inactive]
        linarith

/-- Fully concrete illustration of the boundary indifference: `alpha = 4/5`,
`beta = 3/5`, and independent signals `rho = alpha * beta = 12/25`.  The two distinct
profiles are both equilibria, as allowed by the revised manuscript. -/
theorem knownCorrelation_boundary_example :
    IsNoSharingNash (4 / 5 : ℝ) (3 / 5 : ℝ) (12 / 25 : ℝ) follow follow ∧
    IsNoSharingNash (4 / 5 : ℝ) (3 / 5 : ℝ) (12 / 25 : ℝ) follow inactive ∧
    follow ≠ inactive := by
  have hboundary : 3 * (3 / 5 : ℝ) = 4 / 5 + 1 := by norm_num
  have hbeta : 1 / 2 ≤ (3 / 5 : ℝ) := by norm_num
  have horder : (3 / 5 : ℝ) ≤ 4 / 5 := by norm_num
  exact ⟨boundary_two_equilibria _ _ _ hbeta horder hboundary |>.1,
    boundary_two_equilibria _ _ _ hbeta horder hboundary |>.2,
    fun h => by simpa [follow, inactive] using congrFun h true⟩

end TrainSharing.Correlation.Known
