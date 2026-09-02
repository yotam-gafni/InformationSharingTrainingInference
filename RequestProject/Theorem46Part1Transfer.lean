import RequestProject.Theorem46Part1Classification

/-!
# Theorem 4.6(1): the transfer at the level of trade probabilities

`Theorem46Part1Classification.lean` proves the trade-event transfer under *two* conditions
on equilibrium patterns: `PositiveSignalsAgree` for the no-sharing equilibrium and
`NoNegativeSignalAction` for every revealed world.

This file removes the first of them.  It proves that `PositiveSignalsAgree` can be dropped
entirely, provided one uses the manuscript's own reading of the theorem:

* the no-sharing game is played at the **prior mixture** of the correlation cells
  (`rhoBar = ∑ w, prior w * rho w`), and
* the firms' ex-ante payoffs are the ones of the model, so that the premise "train sharing
  Pareto dominates no sharing" — which is part of literal unique IRPO — has content.

Under these "apples-to-apples" hypotheses only the monotonicity condition remains:

> **`tradeProbability_transfer_of_monotone_worlds`.**  If in no revealed world a firm
> takes the significant action after its own negative inference signal, then the consumer
> weakly prefers the no-sharing equilibrium.

`Theorem46Part1NonInverted.lean` then weakens that last condition to the manuscript's
non-inversion assumption (Definition 4.5), which is exactly what Example 4.7 shows to be
necessary.

The three ingredients are:

* `score_tt_pos_of_follow_follow`: at an `A → 1, a → 1` equilibrium the diagonal score
  `W(A,a)` is strictly positive.  Hence Firm 2's participation strictly hurts Firm 1
  there;
* `transfer_of_noSharing_follow_inactive` and `transfer_of_noSharing_inactive_follow`: if
  the no-sharing equilibrium has a single active firm, Pareto domination forces every
  world in which *both* firms act to have prior probability zero, so train sharing cannot
  trade with probability above `1/2`;
* `noSharing_antiFollow_impossible_of_monotone_worlds`: a non-monotone no-sharing
  equilibrium `A → 1, b → 1` at the prior mixture is *incompatible* with monotone
  equilibria in all the worlds, because Firm 2's interim gain after `b` is affine in the
  correlation cell.
-/

namespace TrainSharing.Theorem46.Transfer

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected
open TrainSharing.Theorem46.Upper
open TrainSharing.Theorem46.Classification

/-! ## 1.  Two algebraic cores

Both sign facts below are consequences of the two correlation-free identities
`W(A,b) + W(B,a) = (R₁ - C₁)(α + β - 2ρ)` and
`W(A,a) + W(B,b) = (R₁ - C₁)(1 - α - β + 2ρ)`, in which the two second factors are the
(nonnegative) probabilities of the off-diagonal and diagonal signal cells. -/

/-- Algebraic core of `score_tt_pos_of_follow_follow`. -/
theorem score_tt_pos_core (W11 W10 W01 W00 k d1 d2 : ℝ)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hoff : W10 + W01 = k * d1) (hdiag : W11 + W00 = k * d2)
    (hg1t : 0 < W11 / 2 + W10) (hg2t : 0 < W11 / 2 + W01)
    (hg1f : W01 / 2 + W00 < 0) :
    0 < W11 := by
  by_contra hcon
  push_neg at hcon
  have h10 : 0 < W10 := by linarith
  have h01 : 0 < W01 := by linarith
  have hk : 0 < k * d1 := by linarith
  have hkpos : 0 < k := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith
    · simp [h] at hk
    · exact h
  have : 0 ≤ k * d2 := mul_nonneg (le_of_lt hkpos) hd2
  linarith

/-- Algebraic core of `col_false_pos_of_follow_antiFollow`. -/
theorem col_false_pos_core (W11 W10 W01 W00 k d1 d2 : ℝ)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hoff : W10 + W01 = k * d1) (hdiag : W11 + W00 = k * d2)
    (hsym : W01 ≤ W10)
    (hg1t : 0 < W11 + W10 / 2) (hg2f : 0 < W10 / 2 + W00) :
    0 < W10 + W00 := by
  rcases lt_or_ge W10 0 with h | h
  case inr => linarith
  · exfalso
    have hk : k * d1 < 0 := by linarith
    have hkneg : k < 0 := by
      rcases lt_trichotomy k 0 with h' | h' | h'
      · exact h'
      · simp [h'] at hk
      · nlinarith
    have : k * d2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hkneg) hd2
    linarith

/-! ## 2.  The diagonal score at an `A → 1, a → 1` equilibrium -/

/-- **At an `A → 1, a → 1` strict equilibrium the diagonal score is positive.**

Consequently Firm 2's participation strictly lowers Firm 1's ex-ante payoff there: Firm 1
has to share the market exactly on the cell `(A,a)`, whose score is positive. -/
theorem score_tt_pos_of_follow_follow
    (alpha beta rho reward cost : ℝ)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost follow follow) :
    0 < weightedSharedScore alpha beta rho reward cost true true := by
  have h1 := hnash.1 true
  have h2 := hnash.1 false
  have h3 := hnash.2 true
  simp only [follow, id_eq, if_true, if_false, Bool.false_eq_true] at h1 h2 h3
  rw [weightedFirm1Gain_eq] at h1 h2
  rw [weightedFirm2Gain_eq] at h3
  simp only [id_eq, shareFactor] at h1 h2 h3
  norm_num at h1 h2 h3
  refine score_tt_pos_core _ _ _ _ (reward - cost) (alpha + beta - 2 * rho)
    (1 - alpha - beta + 2 * rho) (by linarith) (by linarith)
    (score_offdiag alpha beta rho reward cost) (score_diag alpha beta rho reward cost)
    (by linarith) (by linarith) (by linarith)

/-- **At an `A → 1, b → 1` strict equilibrium the negative column sum is positive**, i.e.
acting alone after the negative inference signal `b` is strictly profitable for Firm 2. -/
theorem col_false_pos_of_follow_antiFollow
    (alpha beta rho reward cost : ℝ)
    (horder : beta ≤ alpha) (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost follow antiFollow) :
    0 < reward * (1 - beta) - cost * beta := by
  have h1 := hnash.1 true
  have h4 := hnash.2 false
  simp only [follow, antiFollow, id_eq, if_true, Bool.not_false] at h1 h4
  rw [weightedFirm1Gain_eq] at h1
  rw [weightedFirm2Gain_eq] at h4
  simp only [antiFollow, id_eq, shareFactor, Bool.not_true, Bool.not_false] at h1 h4
  norm_num at h1 h4
  have hsym : weightedSharedScore alpha beta rho reward cost false true ≤
      weightedSharedScore alpha beta rho reward cost true false := by
    simp only [weightedSharedScore, conditionalMass]
    norm_num
    nlinarith [mul_nonneg hreward (by linarith : (0:ℝ) ≤ alpha - beta),
      mul_nonneg hcost (by linarith : (0:ℝ) ≤ alpha - beta)]
  have key := col_false_pos_core (weightedSharedScore alpha beta rho reward cost true true)
    (weightedSharedScore alpha beta rho reward cost true false)
    (weightedSharedScore alpha beta rho reward cost false true)
    (weightedSharedScore alpha beta rho reward cost false false)
    (reward - cost) (alpha + beta - 2 * rho) (1 - alpha - beta + 2 * rho)
    (by linarith) (by linarith)
    (score_offdiag alpha beta rho reward cost) (score_diag alpha beta rho reward cost)
    hsym (by linarith) (by linarith)
  have := score_col_false alpha beta rho reward cost
  linarith

/-! ## 3.  Ex-ante payoffs in the monotone patterns -/

/-- Firm 1's payoff at `A → 1, a → 1`: its solo gain, less a quarter of the diagonal
score, which is the market it has to share with Firm 2. -/
theorem payoff1_follow_follow (alpha beta rho reward cost : ℝ) :
    weightedNoSharingPayoff1 alpha beta rho reward cost follow follow =
      (reward * alpha - cost * (1 - alpha)) / 2 -
        weightedSharedScore alpha beta rho reward cost true true / 4 := by
  simp [weightedNoSharingPayoff1, weightedSharedScore, conditionalMass, follow, shareFactor]
  ring

/-- Firm 2's payoff at `A → 1, a → 1`. -/
theorem payoff2_follow_follow (alpha beta rho reward cost : ℝ) :
    weightedNoSharingPayoff2 alpha beta rho reward cost follow follow =
      (reward * beta - cost * (1 - beta)) / 2 -
        weightedSharedScore alpha beta rho reward cost true true / 4 := by
  simp [weightedNoSharingPayoff2, weightedSharedScore, conditionalMass, follow, shareFactor]
  ring

/-- Firm 2's payoff at `A → 0, a → 1`: its correlation-free solo gain. -/
theorem payoff2_inactive_follow (alpha beta rho reward cost : ℝ) :
    weightedNoSharingPayoff2 alpha beta rho reward cost inactive follow =
      (reward * beta - cost * (1 - beta)) / 2 := by
  simp [weightedNoSharingPayoff2, conditionalMass, follow, inactive, shareFactor]
  ring

/-- A firm that never acts earns nothing. -/
theorem payoff1_of_inactive (alpha beta rho reward cost : ℝ) (s2 : Bool → Bool) :
    weightedNoSharingPayoff1 alpha beta rho reward cost inactive s2 = 0 := by
  simp [weightedNoSharingPayoff1, inactive]

/-- A firm that never acts earns nothing. -/
theorem payoff2_of_inactive (alpha beta rho reward cost : ℝ) (s1 : Bool → Bool) :
    weightedNoSharingPayoff2 alpha beta rho reward cost s1 inactive = 0 := by
  simp [weightedNoSharingPayoff2, inactive]

/-! ## 4.  Trade probabilities of the monotone patterns -/

/-- The trade event of `A → 1, a → 0` has probability exactly one half. -/
theorem tradeProbability_follow_inactive
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) :
    preferredProbability (parameterInferenceLaw p hp)
      (TrainSharing.Theorem43.tradeEvent follow inactive) = 1 / 2 := by
  have h := (parameterInferenceLaw_marginals p hp).1
  simp only [preferredProbability, TrainSharing.Theorem43.tradeEvent, follow, inactive,
    Fintype.sum_prod_type, id_eq] at *
  simp only [Bool.or_false] at *
  rw [Fintype.sum_bool] at *
  norm_num at *
  linarith

/-- The trade event of `A → 0, a → 1` has probability exactly one half. -/
theorem tradeProbability_inactive_follow
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) :
    preferredProbability (parameterInferenceLaw p hp)
      (TrainSharing.Theorem43.tradeEvent inactive follow) = 1 / 2 := by
  have h := (parameterInferenceLaw_marginals p hp).2.2.1
  simp only [preferredProbability, TrainSharing.Theorem43.tradeEvent, follow, inactive,
    Fintype.sum_prod_type, id_eq] at *
  simp only [Bool.false_or] at *
  rw [Fintype.sum_bool] at *
  norm_num at *
  linarith

/-- The all-inactive profile never trades. -/
theorem tradeProbability_inactive_inactive
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) :
    preferredProbability (parameterInferenceLaw p hp)
      (TrainSharing.Theorem43.tradeEvent inactive inactive) = 0 := by
  simp [preferredProbability, TrainSharing.Theorem43.tradeEvent, inactive]

/-- Any monotone pattern other than `A → 1, a → 1` trades with probability at most one
half. -/
theorem tradeProbability_le_half_of_single_active
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) (s1 s2 : Bool → Bool)
    (h : (s1 = inactive ∧ s2 = inactive) ∨ (s1 = follow ∧ s2 = inactive) ∨
      (s1 = inactive ∧ s2 = follow)) :
    preferredProbability (parameterInferenceLaw p hp)
      (TrainSharing.Theorem43.tradeEvent s1 s2) ≤ 1 / 2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · rw [tradeProbability_inactive_inactive]; norm_num
  · rw [tradeProbability_follow_inactive]
  · rw [tradeProbability_inactive_follow]

/-! ## 5.  Classification of the monotone equilibria -/

/-- Under `NoNegativeSignalAction` only four of the seven strict-equilibrium patterns
survive. -/
theorem monotone_classification
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2) :
    (s1 = inactive ∧ s2 = inactive) ∨ (s1 = follow ∧ s2 = inactive) ∨
      (s1 = inactive ∧ s2 = follow) ∨ (s1 = follow ∧ s2 = follow) := by
  obtain ⟨hm1, hm2⟩ := hmono
  rcases strict_equilibrium_classification alpha beta rho reward cost halpha hbeta horder
      hreward hcost hrho0 hrhoa hrhob s1 s2 hnash with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
  · rw [h2] at hm2; exact absurd hm2 (by decide)
  · rw [h2] at hm2; exact absurd hm2 (by decide)
  · rw [h2] at hm2; exact absurd hm2 (by decide)

/-! ## 6.  A non-monotone no-sharing equilibrium is impossible

Firm 2's interim gain after `b`, against Firm 1 following its signal, is an affine
function of the correlation cell.  If every world's equilibrium is monotone, that gain is
negative in every world, hence negative at the prior mixture — but at the mixture the
no-sharing equilibrium `A → 1, b → 1` requires it to be positive. -/

/-- Firm 2's interim gain after `b` against `A → 1` is affine in the correlation cell. -/
theorem weightedFirm2Gain_follow_false_affine (alpha beta rho reward cost : ℝ) :
    weightedFirm2Gain alpha beta rho reward cost follow false =
      (reward - cost) / 4 * rho +
        ((reward * alpha - cost * beta) / 4 + reward * (1 - alpha - beta) / 2) := by
  simp [weightedFirm2Gain, conditionalMass, follow, shareFactor]
  ring

/-- If acting alone after the negative inference signal is strictly profitable for Firm 2,
then at a monotone strict equilibrium the primary firm must act after `A`. -/
theorem monotone_firm1_follow
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hcol : 0 < reward * (1 - beta) - cost * beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2) :
    s1 = follow := by
  have hgain := hnash.2 false
  rw [hmono.2] at hgain
  simp only [if_false, Bool.false_eq_true] at hgain
  rcases monotone_classification alpha beta rho reward cost halpha hbeta horder hreward
      hcost hrho0 hrhoa hrhob s1 s2 hnash hmono with
      ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · exfalso
    rw [h1, soloGain2_false] at hgain
    linarith
  · exact h1
  · exfalso
    rw [h1, soloGain2_false] at hgain
    linarith
  · exact h1

/-- **No non-monotone no-sharing equilibrium above monotone worlds.**  If the no-sharing
game is played at the prior mixture of the correlation cells and every world's selected
profile is a monotone strict equilibrium, then the no-sharing equilibrium cannot be
`A → 1, b → 1`. -/
theorem noSharing_antiFollow_impossible_of_monotone_worlds
    {W : Type} [Fintype W] (prior : FiniteLaw W)
    (rho : W → ℝ) (alpha beta rhoBar reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ rho w) (hrhoa : ∀ w, rho w ≤ alpha) (hrhob : ∀ w, rho w ≤ beta)
    (hbar0 : 0 ≤ rhoBar) (hbara : rhoBar ≤ alpha) (hbarb : rhoBar ≤ beta)
    (hbar1 : 0 ≤ 1 - alpha - beta + rhoBar)
    (hbar : rhoBar = ∑ w, prior.mass w * rho w)
    (hnoNash : IsStrictWeightedNash alpha beta rhoBar reward cost follow antiFollow)
    (t1 t2 : W → Bool → Bool)
    (htrain : ∀ w, IsStrictWeightedNash alpha beta (rho w) reward cost (t1 w) (t2 w))
    (hmono : ∀ w, NoNegativeSignalAction (t1 w) (t2 w)) :
    False := by
  -- Acting alone after `b` is strictly profitable, so every world has `A → 1`.
  have hcol : 0 < reward * (1 - beta) - cost * beta :=
    col_false_pos_of_follow_antiFollow alpha beta rhoBar reward cost horder hreward hcost
      hbar0 hbara hbarb hbar1 hnoNash
  have hfollow : ∀ w, t1 w = follow := fun w =>
    monotone_firm1_follow alpha beta (rho w) reward cost halpha hbeta horder hreward hcost
      (hrho0 w) (hrhoa w) (hrhob w) hcol (t1 w) (t2 w) (htrain w) (hmono w)
  -- In every world Firm 2 strictly prefers to stay out after `b`.
  have hneg : ∀ w, weightedFirm2Gain alpha beta (rho w) reward cost follow false < 0 := by
    intro w
    have hgain := (htrain w).2 false
    rw [(hmono w).2] at hgain
    simp only [if_false, Bool.false_eq_true] at hgain
    rw [hfollow w] at hgain
    exact hgain
  -- At the prior mixture it strictly prefers to act after `b`.
  have hpos : 0 < weightedFirm2Gain alpha beta rhoBar reward cost follow false := by
    have hgain := hnoNash.2 false
    simpa [antiFollow] using hgain
  -- The gain is affine in the correlation cell, so it averages.
  have haffine : ∀ x : ℝ, weightedFirm2Gain alpha beta x reward cost follow false =
      (reward - cost) / 4 * x +
        ((reward * alpha - cost * beta) / 4 + reward * (1 - alpha - beta) / 2) :=
    fun x => weightedFirm2Gain_follow_false_affine alpha beta x reward cost
  have hsum : ∑ w, prior.mass w *
      weightedFirm2Gain alpha beta (rho w) reward cost follow false =
      weightedFirm2Gain alpha beta rhoBar reward cost follow false := by
    simp only [haffine]
    set c : ℝ := (reward - cost) / 4 with hc
    set K : ℝ := (reward * alpha - cost * beta) / 4 + reward * (1 - alpha - beta) / 2 with hK
    have key : ∑ w, prior.mass w * (c * rho w + K)
        = c * (∑ w, prior.mass w * rho w) + K * (∑ w, prior.mass w) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [key, prior.total, hbar]
    ring
  have hle : ∑ w, prior.mass w *
      weightedFirm2Gain alpha beta (rho w) reward cost follow false ≤ 0 := by
    refine Finset.sum_nonpos fun w _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (prior.nonneg w) (le_of_lt (hneg w))
  rw [hsum] at hle
  linarith

/-! ## 7.  A single active firm under no sharing -/

/-- The share of the market that Firm 1 has to give up to Firm 2 in a world where both
firms act after their positive signals. -/
noncomputable def sharedPenalty (alpha beta rho reward cost : ℝ) (s1 s2 : Bool → Bool) : ℝ :=
  if s1 true && s2 true then weightedSharedScore alpha beta rho reward cost true true else 0

/-- The shared market is worth something: the penalty is nonnegative. -/
theorem sharedPenalty_nonneg
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2) :
    0 ≤ sharedPenalty alpha beta rho reward cost s1 s2 := by
  unfold sharedPenalty
  rcases monotone_classification alpha beta rho reward cost halpha hbeta horder hreward
      hcost hrho0 hrhoa hrhob s1 s2 hnash hmono with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · norm_num [inactive]
  · norm_num [follow, inactive]
  · norm_num [follow, inactive]
  · simp only [follow, id_eq, Bool.and_self, if_true]
    exact le_of_lt (score_tt_pos_of_follow_follow alpha beta rho reward cost hrho0 hrhoa
      hrhob hrho1 hnash)

/-- When both firms act after their positive signals the shared market is strictly
valuable. -/
theorem sharedPenalty_pos_of_both
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hrho1 : 0 ≤ 1 - alpha - beta + rho)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2)
    (hboth : (s1 true && s2 true) = true) :
    0 < sharedPenalty alpha beta rho reward cost s1 s2 := by
  rcases monotone_classification alpha beta rho reward cost halpha hbeta horder hreward
      hcost hrho0 hrhoa hrhob s1 s2 hnash hmono with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · exact absurd hboth (by simp [inactive])
  · exact absurd hboth (by simp [follow, inactive])
  · exact absurd hboth (by simp [follow, inactive])
  · unfold sharedPenalty
    rw [if_pos hboth]
    exact score_tt_pos_of_follow_follow alpha beta rho reward cost hrho0 hrhoa hrhob
      hrho1 hnash

/-- Firm 1's ex-ante payoff at a monotone strict equilibrium is its solo gain, less the
shared market. -/
theorem payoff1_le_solo_sub_penalty
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hsolo : 0 ≤ (reward * alpha - cost * (1 - alpha)) / 2)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2) :
    weightedNoSharingPayoff1 alpha beta rho reward cost s1 s2 ≤
      (reward * alpha - cost * (1 - alpha)) / 2 -
        sharedPenalty alpha beta rho reward cost s1 s2 / 4 := by
  unfold sharedPenalty
  rcases monotone_classification alpha beta rho reward cost halpha hbeta horder hreward
      hcost hrho0 hrhoa hrhob s1 s2 hnash hmono with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · rw [payoff1_of_inactive]
    norm_num [inactive]
    linarith
  · rw [payoff1_follow_inactive]
    norm_num [follow, inactive]
  · rw [payoff1_of_inactive]
    norm_num [inactive]
    linarith
  · rw [payoff1_follow_follow]
    norm_num [follow]

/-- Firm 2's ex-ante payoff at a monotone strict equilibrium is its solo gain, less the
shared market. -/
theorem payoff2_le_solo_sub_penalty
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (hsolo : 0 ≤ (reward * beta - cost * (1 - beta)) / 2)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2) :
    weightedNoSharingPayoff2 alpha beta rho reward cost s1 s2 ≤
      (reward * beta - cost * (1 - beta)) / 2 -
        sharedPenalty alpha beta rho reward cost s1 s2 / 4 := by
  unfold sharedPenalty
  rcases monotone_classification alpha beta rho reward cost halpha hbeta horder hreward
      hcost hrho0 hrhoa hrhob s1 s2 hnash hmono with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
  · rw [payoff2_of_inactive]
    norm_num [inactive]
    linarith
  · rw [payoff2_of_inactive]
    norm_num [follow, inactive]
    linarith
  · rw [payoff2_inactive_follow]
    norm_num [follow, inactive]
  · rw [payoff2_follow_follow]
    norm_num [follow]

/-- A monotone equilibrium in which the two firms do not both act after their positive
signals trades with probability at most one half. -/
theorem tradeProbability_le_half_of_not_both
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible)
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2)
    (hmono : NoNegativeSignalAction s1 s2)
    (hnot : (s1 true && s2 true) = false) :
    preferredProbability (parameterInferenceLaw p hp)
      (TrainSharing.Theorem43.tradeEvent s1 s2) ≤ 1 / 2 := by
  refine tradeProbability_le_half_of_single_active p hp s1 s2 ?_
  rcases monotone_classification alpha beta rho reward cost halpha hbeta horder hreward
      hcost hrho0 hrhoa hrhob s1 s2 hnash hmono with
      h | h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    rw [h1, h2] at hnot
    simp [follow] at hnot

/-- **The no-sharing equilibrium `A → 1, a → 0`.**  If train sharing does not lower Firm
1's ex-ante payoff, then every world in which both firms act carries prior probability
zero, so train sharing trades with probability at most one half — exactly the no-sharing
trade probability. -/
theorem transfer_of_noSharing_follow_inactive
    {W : Type} [Fintype W] (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (alpha beta reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ (parameters w).jointTT)
    (hrhoa : ∀ w, (parameters w).jointTT ≤ alpha)
    (hrhob : ∀ w, (parameters w).jointTT ≤ beta)
    (hrho1 : ∀ w, 0 ≤ 1 - alpha - beta + (parameters w).jointTT)
    (t1 t2 : W → Bool → Bool)
    (htrain : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (t1 w) (t2 w))
    (hmono : ∀ w, NoNegativeSignalAction (t1 w) (t2 w))
    (hsolo : 0 < (reward * alpha - cost * (1 - alpha)) / 2)
    (hdom : (reward * alpha - cost * (1 - alpha)) / 2 ≤
      ∑ w, prior.mass w * weightedNoSharingPayoff1 alpha beta ((parameters w).jointTT)
        reward cost (t1 w) (t2 w)) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤ 1 / 2 := by
  set pen : W → ℝ := fun w =>
    sharedPenalty alpha beta ((parameters w).jointTT) reward cost (t1 w) (t2 w) with hpen
  have hpen_nonneg : ∀ w, 0 ≤ pen w := fun w =>
    sharedPenalty_nonneg alpha beta ((parameters w).jointTT) reward cost halpha hbeta horder
      hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (hrho1 w) (t1 w) (t2 w) (htrain w) (hmono w)
  have hpay : ∀ w, weightedNoSharingPayoff1 alpha beta ((parameters w).jointTT) reward cost
      (t1 w) (t2 w) ≤ (reward * alpha - cost * (1 - alpha)) / 2 - pen w / 4 := fun w =>
    payoff1_le_solo_sub_penalty alpha beta ((parameters w).jointTT) reward cost halpha hbeta
      horder hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (le_of_lt hsolo) (t1 w) (t2 w)
      (htrain w) (hmono w)
  -- averaging the payoff bound
  have hsum1 : ∑ w, prior.mass w * weightedNoSharingPayoff1 alpha beta
      ((parameters w).jointTT) reward cost (t1 w) (t2 w) ≤
      ∑ w, prior.mass w * ((reward * alpha - cost * (1 - alpha)) / 2 - pen w / 4) :=
    Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hpay w) (prior.nonneg w)
  have hsum2 : ∑ w, prior.mass w * ((reward * alpha - cost * (1 - alpha)) / 2 - pen w / 4) =
      (reward * alpha - cost * (1 - alpha)) / 2 - (∑ w, prior.mass w * pen w) / 4 := by
    have key : ∑ w, prior.mass w * ((reward * alpha - cost * (1 - alpha)) / 2 - pen w / 4)
        = (reward * alpha - cost * (1 - alpha)) / 2 * (∑ w, prior.mass w) - (∑ w, prior.mass w * pen w) / 4 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [key, prior.total]
    ring
  have hnonpos : ∑ w, prior.mass w * pen w ≤ 0 := by
    rw [hsum2] at hsum1
    linarith
  have hzero : ∀ w ∈ Finset.univ, prior.mass w * pen w = 0 := by
    have hterm : ∀ w ∈ (Finset.univ : Finset W), 0 ≤ prior.mass w * pen w := fun w _ =>
      mul_nonneg (prior.nonneg w) (hpen_nonneg w)
    have hsumzero : ∑ w, prior.mass w * pen w = 0 :=
      le_antisymm hnonpos (Finset.sum_nonneg hterm)
    exact (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsumzero
  -- now bound the trade probability world by world
  unfold correlationEventProbability
  have hbound : ∀ w ∈ (Finset.univ : Finset W),
      prior.mass w * preferredProbability (parameterInferenceLaw (parameters w) (feasible w))
        (TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤ prior.mass w * (1 / 2) := by
    intro w _
    by_cases hb : (t1 w true && t2 w true) = true
    · have hpos : 0 < pen w :=
        sharedPenalty_pos_of_both alpha beta ((parameters w).jointTT) reward cost halpha
          hbeta horder hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (hrho1 w) (t1 w) (t2 w)
          (htrain w) (hmono w) hb
      have hm : prior.mass w = 0 := by
        have := hzero w (Finset.mem_univ w)
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h (ne_of_gt hpos)
      rw [hm]
      ring_nf
      rfl
    · have hnot : (t1 w true && t2 w true) = false := by
        simpa using hb
      exact mul_le_mul_of_nonneg_left
        (tradeProbability_le_half_of_not_both (parameters w) (feasible w) alpha beta
          ((parameters w).jointTT) reward cost halpha hbeta horder hreward hcost (hrho0 w)
          (hrhoa w) (hrhob w) (t1 w) (t2 w) (htrain w) (hmono w) hnot)
        (prior.nonneg w)
  calc ∑ w, prior.mass w * preferredProbability
        (parameterInferenceLaw (parameters w) (feasible w))
        (TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w))
      ≤ ∑ w, prior.mass w * (1 / 2 : ℝ) := Finset.sum_le_sum hbound
    _ = 1 / 2 := by rw [← Finset.sum_mul, prior.total]; ring

/-- **The no-sharing equilibrium `A → 0, a → 1`**, the mirror image of
`transfer_of_noSharing_follow_inactive`. -/
theorem transfer_of_noSharing_inactive_follow
    {W : Type} [Fintype W] (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (alpha beta reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ (parameters w).jointTT)
    (hrhoa : ∀ w, (parameters w).jointTT ≤ alpha)
    (hrhob : ∀ w, (parameters w).jointTT ≤ beta)
    (hrho1 : ∀ w, 0 ≤ 1 - alpha - beta + (parameters w).jointTT)
    (t1 t2 : W → Bool → Bool)
    (htrain : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (t1 w) (t2 w))
    (hmono : ∀ w, NoNegativeSignalAction (t1 w) (t2 w))
    (hsolo : 0 < (reward * beta - cost * (1 - beta)) / 2)
    (hdom : (reward * beta - cost * (1 - beta)) / 2 ≤
      ∑ w, prior.mass w * weightedNoSharingPayoff2 alpha beta ((parameters w).jointTT)
        reward cost (t1 w) (t2 w)) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤ 1 / 2 := by
  set pen : W → ℝ := fun w =>
    sharedPenalty alpha beta ((parameters w).jointTT) reward cost (t1 w) (t2 w) with hpen
  have hpen_nonneg : ∀ w, 0 ≤ pen w := fun w =>
    sharedPenalty_nonneg alpha beta ((parameters w).jointTT) reward cost halpha hbeta horder
      hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (hrho1 w) (t1 w) (t2 w) (htrain w) (hmono w)
  have hpay : ∀ w, weightedNoSharingPayoff2 alpha beta ((parameters w).jointTT) reward cost
      (t1 w) (t2 w) ≤ (reward * beta - cost * (1 - beta)) / 2 - pen w / 4 := fun w =>
    payoff2_le_solo_sub_penalty alpha beta ((parameters w).jointTT) reward cost halpha hbeta
      horder hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (le_of_lt hsolo) (t1 w) (t2 w)
      (htrain w) (hmono w)
  -- averaging the payoff bound
  have hsum1 : ∑ w, prior.mass w * weightedNoSharingPayoff2 alpha beta
      ((parameters w).jointTT) reward cost (t1 w) (t2 w) ≤
      ∑ w, prior.mass w * ((reward * beta - cost * (1 - beta)) / 2 - pen w / 4) :=
    Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hpay w) (prior.nonneg w)
  have hsum2 : ∑ w, prior.mass w * ((reward * beta - cost * (1 - beta)) / 2 - pen w / 4) =
      (reward * beta - cost * (1 - beta)) / 2 - (∑ w, prior.mass w * pen w) / 4 := by
    have key : ∑ w, prior.mass w * ((reward * beta - cost * (1 - beta)) / 2 - pen w / 4)
        = (reward * beta - cost * (1 - beta)) / 2 * (∑ w, prior.mass w) - (∑ w, prior.mass w * pen w) / 4 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [key, prior.total]
    ring
  have hnonpos : ∑ w, prior.mass w * pen w ≤ 0 := by
    rw [hsum2] at hsum1
    linarith
  have hzero : ∀ w ∈ Finset.univ, prior.mass w * pen w = 0 := by
    have hterm : ∀ w ∈ (Finset.univ : Finset W), 0 ≤ prior.mass w * pen w := fun w _ =>
      mul_nonneg (prior.nonneg w) (hpen_nonneg w)
    have hsumzero : ∑ w, prior.mass w * pen w = 0 :=
      le_antisymm hnonpos (Finset.sum_nonneg hterm)
    exact (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsumzero
  -- now bound the trade probability world by world
  unfold correlationEventProbability
  have hbound : ∀ w ∈ (Finset.univ : Finset W),
      prior.mass w * preferredProbability (parameterInferenceLaw (parameters w) (feasible w))
        (TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤ prior.mass w * (1 / 2) := by
    intro w _
    by_cases hb : (t1 w true && t2 w true) = true
    · have hpos : 0 < pen w :=
        sharedPenalty_pos_of_both alpha beta ((parameters w).jointTT) reward cost halpha
          hbeta horder hreward hcost (hrho0 w) (hrhoa w) (hrhob w) (hrho1 w) (t1 w) (t2 w)
          (htrain w) (hmono w) hb
      have hm : prior.mass w = 0 := by
        have := hzero w (Finset.mem_univ w)
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h (ne_of_gt hpos)
      rw [hm]
      ring_nf
      rfl
    · have hnot : (t1 w true && t2 w true) = false := by
        simpa using hb
      exact mul_le_mul_of_nonneg_left
        (tradeProbability_le_half_of_not_both (parameters w) (feasible w) alpha beta
          ((parameters w).jointTT) reward cost halpha hbeta horder hreward hcost (hrho0 w)
          (hrhoa w) (hrhob w) (t1 w) (t2 w) (htrain w) (hmono w) hnot)
        (prior.nonneg w)
  calc ∑ w, prior.mass w * preferredProbability
        (parameterInferenceLaw (parameters w) (feasible w))
        (TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w))
      ≤ ∑ w, prior.mass w * (1 / 2 : ℝ) := Finset.sum_le_sum hbound
    _ = 1 / 2 := by rw [← Finset.sum_mul, prior.total]; ring

/-! ## 8.  The tight transfer theorem -/

/-- A no-sharing equilibrium with a single active firm trades with probability one half in
every correlation world, hence ex ante. -/
theorem correlationEventProbability_single_active
    {W : Type} [Fintype W] (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (n1 n2 : Bool → Bool)
    (h : (n1 = follow ∧ n2 = inactive) ∨ (n1 = inactive ∧ n2 = follow)) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) = 1 / 2 := by
  have hval : ∀ w, preferredProbability (parameterInferenceLaw (parameters w) (feasible w))
      (TrainSharing.Theorem43.tradeEvent n1 n2) = 1 / 2 := by
    intro w
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · exact tradeProbability_follow_inactive (parameters w) (feasible w)
    · exact tradeProbability_inactive_follow (parameters w) (feasible w)
  unfold correlationEventProbability
  simp only [hval]
  rw [← Finset.sum_mul, prior.total]
  ring

/-- **The transfer at the level of trade probabilities.**

Standing assumptions of Section 3; the no-sharing game is played at the prior mixture
`rhoBar` of the correlation cells; the selected no-sharing profile and every selected
world profile are strict equilibria; train sharing does not lower either firm's ex-ante
payoff (this is part of literal unique IRPO); and **in no world does a firm take the
significant action after its own negative inference signal**.

Then the normalized opportunity-seeking consumer weakly prefers the no-sharing
equilibrium.  No condition on the no-sharing equilibrium pattern is needed. -/
theorem tradeProbability_transfer_of_monotone_worlds
    {W : Type} [Fintype W] (prior : FiniteLaw W)
    (parameters : W → TrainSharing.Correlation.Parameters)
    (feasible : ∀ w, (parameters w).Feasible)
    (alpha beta rhoBar reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : ∀ w, 0 ≤ (parameters w).jointTT)
    (hrhoa : ∀ w, (parameters w).jointTT ≤ alpha)
    (hrhob : ∀ w, (parameters w).jointTT ≤ beta)
    (hrho1 : ∀ w, 0 ≤ 1 - alpha - beta + (parameters w).jointTT)
    (hbar0 : 0 ≤ rhoBar) (hbara : rhoBar ≤ alpha) (hbarb : rhoBar ≤ beta)
    (hbar1 : 0 ≤ 1 - alpha - beta + rhoBar)
    (hbar : rhoBar = ∑ w, prior.mass w * (parameters w).jointTT)
    (n1 n2 : Bool → Bool) (t1 t2 : W → Bool → Bool)
    (hno : IsStrictWeightedNash alpha beta rhoBar reward cost n1 n2)
    (htrain : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (t1 w) (t2 w))
    (hmono : ∀ w, NoNegativeSignalAction (t1 w) (t2 w))
    (hdom1 : weightedNoSharingPayoff1 alpha beta rhoBar reward cost n1 n2 ≤
      ∑ w, prior.mass w * weightedNoSharingPayoff1 alpha beta ((parameters w).jointTT)
        reward cost (t1 w) (t2 w))
    (hdom2 : weightedNoSharingPayoff2 alpha beta rhoBar reward cost n1 n2 ≤
      ∑ w, prior.mass w * weightedNoSharingPayoff2 alpha beta ((parameters w).jointTT)
        reward cost (t1 w) (t2 w)) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
  -- a pointwise event inclusion always suffices
  have hpointwise : (∀ w q, TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w) q = true →
      TrainSharing.Theorem43.tradeEvent n1 n2 q = true) →
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
    intro h
    exact correlationTradeProbability_transfer prior _ t1 t2 n1 n2 h
  -- the transfer of `Theorem46Part1Classification` applies whenever the two firms agree about
  -- their positive signals under no sharing
  have hagreeCase : PositiveSignalsAgree n1 n2 →
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (t1 w) (t2 w)) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
    intro hagree
    refine hpointwise fun w q hq => ?_
    exact tradeEvent_transfer_of_monotone_patterns alpha beta rhoBar ((parameters w).jointTT) reward
      cost halpha hbeta horder hreward hcost hbar0 hbara hbarb (hrho0 w) (hrhoa w) (hrhob w)
      (hrho1 w) n1 n2 (t1 w) (t2 w) hno (htrain w) hagree (hmono w) q hq
  rcases strict_equilibrium_classification alpha beta rhoBar reward cost halpha hbeta horder
      hreward hcost hbar0 hbara hbarb n1 n2 hno with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- nobody acts
    exact hagreeCase (by simp [PositiveSignalsAgree, h1, h2])
  · -- `A → 1, a → 0`
    subst h1; subst h2
    rw [correlationEventProbability_single_active prior parameters feasible follow inactive
      (Or.inl ⟨rfl, rfl⟩)]
    have hsolo : 0 < (reward * alpha - cost * (1 - alpha)) / 2 := by
      have h := hno.1 true
      simp only [follow, id_eq, if_true] at h
      rwa [soloGain1] at h
    refine transfer_of_noSharing_follow_inactive prior parameters feasible alpha beta reward
      cost halpha hbeta horder hreward hcost hrho0 hrhoa hrhob hrho1 t1 t2 htrain hmono
      hsolo ?_
    rwa [payoff1_follow_inactive] at hdom1
  · -- `A → 0, a → 1`
    subst h1; subst h2
    rw [correlationEventProbability_single_active prior parameters feasible inactive follow
      (Or.inr ⟨rfl, rfl⟩)]
    have hsolo : 0 < (reward * beta - cost * (1 - beta)) / 2 := by
      have h := hno.2 true
      simp only [follow, id_eq, if_true] at h
      rwa [soloGain2] at h
    refine transfer_of_noSharing_inactive_follow prior parameters feasible alpha beta reward
      cost halpha hbeta horder hreward hcost hrho0 hrhoa hrhob hrho1 t1 t2 htrain hmono
      hsolo ?_
    rwa [payoff2_inactive_follow] at hdom2
  · -- `A → 1, a → 1`
    exact hagreeCase (by simp [PositiveSignalsAgree, h1, h2])
  · -- `A → 1, b → 1`: impossible above monotone worlds
    exfalso
    subst h1; subst h2
    exact noSharing_antiFollow_impossible_of_monotone_worlds prior
      (fun w => (parameters w).jointTT) alpha beta rhoBar reward cost halpha hbeta horder
      hreward hcost hrho0 hrhoa hrhob hbar0 hbara hbarb hbar1 hbar hno t1 t2 htrain hmono
  · -- `A → 1, a → 1, b → 1`: the no-sharing equilibrium always trades
    subst h2
    exact hpointwise fun w q _ => by
      simp only [TrainSharing.Theorem43.tradeEvent, Bool.or_true]
  · -- everybody always acts
    subst h2
    exact hpointwise fun w q _ => by
      simp only [TrainSharing.Theorem43.tradeEvent, Bool.or_true]

/-! ## 9.  Two conveniences

The prior mixture of feasible correlation cells is feasible, and — by the classification —
`NoNegativeSignalAction` is entirely a statement about the *secondary* firm. -/

/-- A prior mixture of feasible correlation cells is feasible. -/
theorem mixture_feasible {W : Type} [Fintype W] (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta rhoBar : ℝ)
    (h0 : ∀ w, 0 ≤ rho w) (ha : ∀ w, rho w ≤ alpha) (hb : ∀ w, rho w ≤ beta)
    (h1 : ∀ w, 0 ≤ 1 - alpha - beta + rho w)
    (hbar : rhoBar = ∑ w, prior.mass w * rho w) :
    0 ≤ rhoBar ∧ rhoBar ≤ alpha ∧ rhoBar ≤ beta ∧ 0 ≤ 1 - alpha - beta + rhoBar := by
  have hsum : ∀ f : W → ℝ, (∀ w, 0 ≤ f w) → 0 ≤ ∑ w, prior.mass w * f w := by
    intro f hf
    exact Finset.sum_nonneg fun w _ => mul_nonneg (prior.nonneg w) (hf w)
  have hconst : ∀ c : ℝ, ∑ w, prior.mass w * c = c := by
    intro c
    rw [← Finset.sum_mul, prior.total]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hbar]; exact hsum rho h0
  · rw [hbar, ← hconst alpha]
    exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (ha w) (prior.nonneg w)
  · rw [hbar, ← hconst beta]
    exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hb w) (prior.nonneg w)
  · have := hsum (fun w => 1 - alpha - beta + rho w) h1
    have heq : ∑ w, prior.mass w * (1 - alpha - beta + rho w) =
        (1 - alpha - beta) * (∑ w, prior.mass w) + ∑ w, prior.mass w * rho w := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [heq, prior.total] at this
    rw [hbar]
    linarith

/-- By the classification, no firm acts after its negative signal as soon as the
*secondary* firm does not: only the everywhere-active pattern has Firm 1 acting after
`B`, and there Firm 2 acts after `b` as well. -/
theorem noNegativeSignalAction_iff_firm2
    (alpha beta rho reward cost : ℝ)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (hrho0 : 0 ≤ rho) (hrhoa : rho ≤ alpha) (hrhob : rho ≤ beta)
    (s1 s2 : Bool → Bool)
    (hnash : IsStrictWeightedNash alpha beta rho reward cost s1 s2) :
    NoNegativeSignalAction s1 s2 ↔ s2 false = false := by
  constructor
  · exact fun h => h.2
  · intro h2
    refine ⟨?_, h2⟩
    rcases strict_equilibrium_classification alpha beta rho reward cost halpha hbeta horder
        hreward hcost hrho0 hrhoa hrhob s1 s2 hnash with
        ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ <;>
      first
        | (rw [h1]; rfl)
        | (rw [hb] at h2; exact absurd h2 (by decide))

end TrainSharing.Theorem46.Transfer
