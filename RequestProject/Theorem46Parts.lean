import RequestProject.Theorem46Part1Transfer

/-!
# Theorem 4.6: the model-payoff selection, conclusion (2), and the monotone case of (1)

The manuscript states Theorem 4.6 as a single statement with two conclusions.  They have
very different status, and this file separates them.

* `ModelPayoffs` fixes the manuscript's reading of an equilibrium selection: each
  contract's ex-ante payoff vector is the significant-action payoff vector of its selected
  profile, and the no-sharing game is played at the **prior mixture** of the correlation
  cells.  Every statement about conclusion (1) is made under this hypothesis, so that the
  premise "train sharing is IRPO" — hence Pareto dominates no sharing — has content.

* **Theorem 4.6(2).**  `theorem4_6_part2` is the factor-two bound.  It needs nothing
  beyond the model and the manuscript's own hypothesis that train sharing is literally the
  unique IRPO contract; in particular no condition on which equilibrium patterns occur.
  (It is `Theorem46UpperBound.theorem4_6_factor_two_from_model`, restated here so that the
  two conclusions sit side by side.)

* **Theorem 4.6(1), monotone case.**  `part1_transfer_of_monotone_worlds` is the consumer
  comparison under the condition that in no correlation world does the secondary firm act
  after its own negative inference signal.  `Theorem46Part1NonInverted.lean` weakens that
  condition to the manuscript's non-inversion assumption (Definition 4.5), which is the
  form in which conclusion (1) is stated, and Example 4.7 shows that non-inversion cannot
  be dropped.
-/

namespace TrainSharing.Theorem46.Parts

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected
open TrainSharing.Theorem46.Upper
open TrainSharing.Theorem46.Classification
open TrainSharing.Theorem46.Transfer

/-- The selected equilibria are the model's.  Each contract's ex-ante payoff vector is the
significant-action payoff vector of its selected profile, and the no-sharing game is played
at the prior mixture `rhoBar` of the correlation cells — the manuscript's reading. -/
structure ModelPayoffs {W : Type} [Fintype W] (S : EquilibriumSelection W)
    (prior : FiniteLaw W) (parameters : W → TrainSharing.Correlation.Parameters)
    (alpha beta rhoBar reward cost : ℝ) : Prop where
  /-- No sharing is played at the prior mixture of the correlation cells. -/
  mixture : rhoBar = ∑ w, prior.mass w * (parameters w).jointTT
  /-- Firm 1's no-sharing payoff. -/
  noSharing1 : S.utility .noSharing .firm1 =
    weightedNoSharingPayoff1 alpha beta rhoBar reward cost S.noFirm1 S.noFirm2
  /-- Firm 2's no-sharing payoff. -/
  noSharing2 : S.utility .noSharing .firm2 =
    weightedNoSharingPayoff2 alpha beta rhoBar reward cost S.noFirm1 S.noFirm2
  /-- Firm 1's train-sharing payoff, averaged over the revealed worlds. -/
  train1 : S.utility .trainSharing .firm1 =
    ∑ w, prior.mass w * weightedNoSharingPayoff1 alpha beta ((parameters w).jointTT)
      reward cost (S.trainFirm1 w) (S.trainFirm2 w)
  /-- Firm 2's train-sharing payoff, averaged over the revealed worlds. -/
  train2 : S.utility .trainSharing .firm2 =
    ∑ w, prior.mass w * weightedNoSharingPayoff2 alpha beta ((parameters w).jointTT)
      reward cost (S.trainFirm1 w) (S.trainFirm2 w)

section

variable {W : Type} [Fintype W]
variable (prior : FiniteLaw W)
variable (parameters : W → TrainSharing.Correlation.Parameters)
variable (feasible : ∀ w, (parameters w).Feasible)
variable (S : EquilibriumSelection W)
variable (alpha beta rhoBar reward cost : ℝ)

-- Feasibility of each world's correlation cell, in the four-inequality form used by the
-- significant-action calculations.
omit [Fintype W] in
private theorem cell_bounds
    (feasible : ∀ w, (parameters w).Feasible)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta) :
    (∀ w, 0 ≤ (parameters w).jointTT) ∧ (∀ w, (parameters w).jointTT ≤ alpha) ∧
      (∀ w, (parameters w).jointTT ≤ beta) ∧
      (∀ w, 0 ≤ 1 - alpha - beta + (parameters w).jointTT) := by
  refine ⟨fun w => le_trans (le_max_left _ _) (feasible w).1, fun w => ?_, fun w => ?_,
    fun w => ?_⟩
  · have h := le_trans (feasible w).2 (min_le_left _ _)
    rw [halphaw w] at h
    exact h
  · have h := le_trans (feasible w).2 (min_le_right _ _)
    rw [hbetaw w] at h
    exact h
  · have h := le_trans (le_max_right (0 : ℝ)
      ((parameters w).alpha + (parameters w).beta - 1)) (feasible w).1
    rw [halphaw w, hbetaw w] at h
    linarith

/-! ## Theorem 4.6(1), for monotone world equilibria -/

/-- **Theorem 4.6(1), monotone case.**

With significant-action utilities, accuracies `alpha ≥ beta ≥ 1/2`, nonnegative reward and
mistake cost, a fixed equilibrium selection whose payoffs are the model's and whose
no-sharing game is played at the prior mixture of the correlation cells, train sharing
literally the unique IRPO contract, strict equilibria throughout, **and**

> in no correlation world does the secondary firm take the significant action after its own
> negative inference signal,

the normalized opportunity-seeking consumer weakly prefers the selected no-sharing
equilibrium.

The last condition is weakened to non-inversion in
`Theorem46Part1NonInverted.theorem4_6_part1_nonInverted`, and non-inversion itself cannot
be dropped: `example4_7_refutes_part1`. -/
theorem part1_transfer_of_monotone_worlds
    (hunique : TrainSharing.Theorem46.Selected.IsUniquelyIRPO S Contract.trainSharing)
    (hmodel : ModelPayoffs S prior parameters alpha beta rhoBar reward cost)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta) (horder : beta ≤ alpha)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta)
    (hnoNash : IsStrictWeightedNash alpha beta rhoBar reward cost S.noFirm1 S.noFirm2)
    (htrainNash : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (S.trainFirm1 w) (S.trainFirm2 w))
    (hmono : ∀ w, S.trainFirm2 w false = false) :
    correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (S.event .trainSharing) ≤
      correlationEventProbability prior
        (fun w => parameterInferenceLaw (parameters w) (feasible w))
        (S.event .noSharing) := by
  obtain ⟨hrho0, hrhoa, hrhob, hrho1⟩ := cell_bounds parameters alpha beta feasible halphaw hbetaw
  obtain ⟨hbar0, hbara, hbarb, hbar1⟩ :=
    mixture_feasible prior (fun w => (parameters w).jointTT) alpha beta rhoBar hrho0 hrhoa
      hrhob hrho1 hmodel.mixture
  -- literal unique IRPO gives Pareto dominance over no sharing
  have hpareto : TrainSharing.Theorem46.Selected.ParetoDominates S Contract.trainSharing Contract.noSharing := by
    rcases hunique.1.1 with h | h
    · exact absurd h (by decide)
    · exact h
  have hdom1 := hpareto Firm.firm1
  have hdom2 := hpareto Firm.firm2
  rw [hmodel.noSharing1, hmodel.train1] at hdom1
  rw [hmodel.noSharing2, hmodel.train2] at hdom2
  -- monotone worlds
  have hmono' : ∀ w, NoNegativeSignalAction (S.trainFirm1 w) (S.trainFirm2 w) := by
    intro w
    refine (noNegativeSignalAction_iff_firm2 alpha beta ((parameters w).jointTT) reward cost
      halpha hbeta horder hreward hcost (hrho0 w) (hrhoa w) (hrhob w) _ _ (htrainNash w)).mpr ?_
    exact hmono w
  rw [S.train_event, S.no_event]
  exact tradeProbability_transfer_of_monotone_worlds prior parameters feasible alpha beta
    rhoBar reward cost halpha hbeta horder hreward hcost hrho0 hrhoa hrhob hrho1 hbar0
    hbara hbarb hbar1 hmodel.mixture S.noFirm1 S.noFirm2 S.trainFirm1 S.trainFirm2 hnoNash
    htrainNash hmono' hdom1 hdom2

/-! ## Theorem 4.6(2) -/

/-- **Theorem 4.6(2).**  Every selected contract equilibrium has trade probability at most
twice that of train sharing.  Unlike conclusion (1) this needs no condition at all on the
equilibrium patterns: only the model, strictness of the world equilibria, and literal
unique IRPO of train sharing. -/
theorem theorem4_6_part2
    (hunique : TrainSharing.Theorem46.Selected.IsUniquelyIRPO S Contract.trainSharing)
    (halpha : 1 / 2 ≤ alpha) (hbeta : 1 / 2 ≤ beta)
    (hreward : 0 ≤ reward) (hcost : 0 ≤ cost)
    (halphaw : ∀ w, (parameters w).alpha = alpha)
    (hbetaw : ∀ w, (parameters w).beta = beta)
    (htrainNash : ∀ w, IsStrictWeightedNash alpha beta ((parameters w).jointTT) reward cost
      (S.trainFirm1 w) (S.trainFirm2 w)) :
    ∀ c : Contract,
      correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event c) ≤
        2 * correlationEventProbability prior
          (fun w => parameterInferenceLaw (parameters w) (feasible w))
          (S.event .trainSharing) :=
  theorem4_6_factor_two_from_model prior parameters feasible S hunique alpha beta reward
    cost halpha hbeta hreward hcost halphaw hbetaw htrainNash

end

end TrainSharing.Theorem46.Parts
