import RequestProject.Theorem46Part1NonInverted

/-!
# The all-acting world: the *selected* reading of Theorem 4.6(1) fails

`Theorem46Part1NonInverted.lean` proves Theorem 4.6(1) under the manuscript's non-inversion
assumption — no world has the equilibrium pattern `a → 0, b → 1` — in two readings:

* the **selected** reading (`theorem4_6_part1_nonInverted`), which additionally
  assumes that no world is all-acting; and
* the **existential** reading (`theorem4_6_part1_existence_nonInverted`), which assumes
  nothing about the all-acting worlds.

This file shows that the extra assumption in the first reading cannot be dropped: with an
all-acting world present the consumer may strictly prefer train sharing to the *selected*
no-sharing equilibrium.  (The existential reading survives, because the all-acting profile
is then also a strict equilibrium of the no-sharing game, and it trades with probability
one; `aa_existence_conclusion_holds` records this for the very same instance.)

## The instance

Accuracies `alpha = 11/20` and `beta = 27/50`, reward `R₁ = 1`, mistake cost `C₁ = 3/4`,
and two correlation worlds:

* world `w₁` (prior `1/20`) with joint positive cell `rho₁ = 49/100`, where **everybody
  always acts**;
* world `w₂` (prior `19/20`) with joint positive cell `rho₂ = 1/10`, where both firms
  follow their inference signals.

Both cells lie in the Fréchet interval `[9/100, 27/50]`, and the no-sharing game is played
against the mixture `rho̅ = 239/2000`, where the selected equilibrium has both firms
following their signals.

Train sharing strictly Pareto dominates no sharing — `(2627, 2361)/32000` against
`(2621, 2341)/32000` — and neither full sharing nor inference sharing is individually
rational against no sharing, so train sharing is literally the unique IRPO contract.  The
secondary firm never acts after `b` *without* also acting after `a`, so the equilibrium is
not inverted.  Nevertheless the consumer strictly prefers train sharing: it trades with
probability `3791/4000 = 0.947...`, against `1851/2000 = 0.9255` for the selected
no-sharing equilibrium.
-/

namespace TrainSharing.Theorem46.AllActing

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected
open TrainSharing.Theorem46.Upper
open TrainSharing.Theorem46.Part1 (alwaysAct)

/-! ## The instance -/

/-- Firm 1's accuracy. -/
noncomputable def aaAlpha : ℝ := 11 / 20
/-- Firm 2's accuracy. -/
noncomputable def aaBeta : ℝ := 27 / 50
/-- Reward for a correct significant action. -/
noncomputable def aaReward : ℝ := 1
/-- Cost of an incorrect significant action. -/
noncomputable def aaCost : ℝ := 3 / 4
/-- The two correlation worlds, indexed by `Bool`. -/
noncomputable def aaRho : Bool → ℝ := fun w => if w then 49 / 100 else 1 / 10
/-- The mixture correlation seen under no sharing. -/
noncomputable def aaRhoBar : ℝ := 239 / 2000

/-- The selected train-sharing strategy of Firm 1: it acts after both signals in the
strongly correlated world, and follows its signal in the other. -/
def aaTrain1 : Bool → Bool → Bool := fun w => if w then alwaysAct else follow
/-- The selected train-sharing strategy of Firm 2: the same. -/
def aaTrain2 : Bool → Bool → Bool := fun w => if w then alwaysAct else follow

/-- The prior over the two correlation worlds: the all-acting world is rare. -/
noncomputable def aaPrior : FiniteLaw Bool where
  mass w := if w then 1 / 20 else 19 / 20
  nonneg w := by cases w <;> norm_num
  total := by norm_num [Fintype.sum_bool]

/-! ## The three games and their selected equilibria -/

theorem aa_equilibrium_world_true :
    IsStrictWeightedNash aaAlpha aaBeta (aaRho true) aaReward aaCost alwaysAct alwaysAct := by
  constructor <;> intro x <;> cases x <;>
    norm_num [weightedFirm1Gain, weightedFirm2Gain, conditionalMass, alwaysAct, shareFactor,
      aaAlpha, aaBeta, aaReward, aaCost, aaRho]

theorem aa_equilibrium_world_false :
    IsStrictWeightedNash aaAlpha aaBeta (aaRho false) aaReward aaCost follow follow := by
  constructor <;> intro x <;> cases x <;>
    norm_num [weightedFirm1Gain, weightedFirm2Gain, conditionalMass, follow, shareFactor,
      aaAlpha, aaBeta, aaReward, aaCost, aaRho]

theorem aa_equilibrium_noSharing :
    IsStrictWeightedNash aaAlpha aaBeta aaRhoBar aaReward aaCost follow follow := by
  constructor <;> intro x <;> cases x <;>
    norm_num [weightedFirm1Gain, weightedFirm2Gain, conditionalMass, follow, shareFactor,
      aaAlpha, aaBeta, aaReward, aaCost, aaRhoBar]

/-! ## Equilibrium payoffs -/

theorem aa_payoff1_world_true :
    weightedNoSharingPayoff1 aaAlpha aaBeta (aaRho true) aaReward aaCost alwaysAct alwaysAct =
      1 / 16 := by
  norm_num [weightedNoSharingPayoff1, conditionalMass, alwaysAct, shareFactor,
    aaAlpha, aaBeta, aaReward, aaCost, aaRho, Fintype.sum_prod_type]

theorem aa_payoff2_world_true :
    weightedNoSharingPayoff2 aaAlpha aaBeta (aaRho true) aaReward aaCost alwaysAct alwaysAct =
      1 / 16 := by
  norm_num [weightedNoSharingPayoff2, conditionalMass, alwaysAct, shareFactor,
    aaAlpha, aaBeta, aaReward, aaCost, aaRho, Fintype.sum_prod_type]

theorem aa_payoff1_world_false :
    weightedNoSharingPayoff1 aaAlpha aaBeta (aaRho false) aaReward aaCost follow follow =
      133 / 1600 := by
  norm_num [weightedNoSharingPayoff1, conditionalMass, follow, shareFactor,
    aaAlpha, aaBeta, aaReward, aaCost, aaRho, Fintype.sum_prod_type]

theorem aa_payoff2_world_false :
    weightedNoSharingPayoff2 aaAlpha aaBeta (aaRho false) aaReward aaCost follow follow =
      119 / 1600 := by
  norm_num [weightedNoSharingPayoff2, conditionalMass, follow, shareFactor,
    aaAlpha, aaBeta, aaReward, aaCost, aaRho, Fintype.sum_prod_type]

theorem aa_payoff1_noSharing :
    weightedNoSharingPayoff1 aaAlpha aaBeta aaRhoBar aaReward aaCost follow follow =
      2621 / 32000 := by
  norm_num [weightedNoSharingPayoff1, conditionalMass, follow, shareFactor,
    aaAlpha, aaBeta, aaReward, aaCost, aaRhoBar, Fintype.sum_prod_type]

theorem aa_payoff2_noSharing :
    weightedNoSharingPayoff2 aaAlpha aaBeta aaRhoBar aaReward aaCost follow follow =
      2341 / 32000 := by
  norm_num [weightedNoSharingPayoff2, conditionalMass, follow, shareFactor,
    aaAlpha, aaBeta, aaReward, aaCost, aaRhoBar, Fintype.sum_prod_type]

theorem aa_fullInfoPayoff_world_true :
    fullInfoPayoff aaAlpha aaBeta (aaRho true) aaReward aaCost = 1 / 16 := by
  norm_num [fullInfoPayoff, weightedSharedScore, conditionalMass,
    aaAlpha, aaBeta, aaReward, aaCost, aaRho, Fintype.sum_prod_type]

theorem aa_fullInfoPayoff_world_false :
    fullInfoPayoff aaAlpha aaBeta (aaRho false) aaReward aaCost = 63 / 800 := by
  norm_num [fullInfoPayoff, weightedSharedScore, conditionalMass,
    aaAlpha, aaBeta, aaReward, aaCost, aaRho, Fintype.sum_prod_type]

theorem aa_fullInfoPayoff_noSharing :
    fullInfoPayoff aaAlpha aaBeta aaRhoBar aaReward aaCost = 2481 / 32000 := by
  norm_num [fullInfoPayoff, weightedSharedScore, conditionalMass,
    aaAlpha, aaBeta, aaReward, aaCost, aaRhoBar, Fintype.sum_prod_type]

/-! ## The correlation parameters of the two worlds -/

/-- The two feasible correlation worlds, presented as parameters of the Section 3 model. -/
noncomputable def aaParams (w : Bool) : TrainSharing.Correlation.Parameters where
  alpha := aaAlpha
  beta := aaBeta
  theta := (aaRho w - aaAlpha * aaBeta) /
    Real.sqrt (aaAlpha * (1 - aaAlpha) * aaBeta * (1 - aaBeta))
  alpha_mem := by constructor <;> norm_num [aaAlpha]
  beta_mem := by constructor <;> norm_num [aaBeta]

theorem aaParams_jointTT (w : Bool) : (aaParams w).jointTT = aaRho w := by
  have hs := TrainSharing.Correlation.Parameters.scale_pos (aaParams w)
  show aaAlpha * aaBeta + ((aaRho w - aaAlpha * aaBeta) /
    Real.sqrt (aaAlpha * (1 - aaAlpha) * aaBeta * (1 - aaBeta))) * (aaParams w).scale =
      aaRho w
  have hscale : (aaParams w).scale =
      Real.sqrt (aaAlpha * (1 - aaAlpha) * aaBeta * (1 - aaBeta)) := rfl
  rw [hscale] at hs ⊢
  rw [div_mul_cancel₀ _ (ne_of_gt hs)]
  ring

theorem aaParams_feasible (w : Bool) : (aaParams w).Feasible := by
  constructor <;> rw [aaParams_jointTT w] <;> cases w <;>
    simp [aaParams, aaAlpha, aaBeta, aaRho] <;> norm_num

/-! ## Consumer trade probabilities -/

theorem aa_mass (w : Bool) (q : Bool × Bool) :
    (parameterInferenceLaw (aaParams w) (aaParams_feasible w)).mass q =
      ((aaParams w).jointMass q + (aaParams w).jointMass (!q.1, !q.2)) / 2 := by
  simp [parameterInferenceLaw, TrainSharing.Correlation.Parameters.world,
    TrainSharing.Correlation.Parameters.signalLaw]
  ring

theorem aa_mass_values (w : Bool) :
    (parameterInferenceLaw (aaParams w) (aaParams_feasible w)).mass (true, true) =
      (if w then 89 else 11) / 200 ∧
    (parameterInferenceLaw (aaParams w) (aaParams_feasible w)).mass (true, false) =
      (if w then 11 else 89) / 200 ∧
    (parameterInferenceLaw (aaParams w) (aaParams_feasible w)).mass (false, true) =
      (if w then 11 else 89) / 200 ∧
    (parameterInferenceLaw (aaParams w) (aaParams_feasible w)).mass (false, false) =
      (if w then 89 else 11) / 200 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [aa_mass]
    simp only [TrainSharing.Correlation.Parameters.jointMass, Bool.not_true, Bool.not_false]
    rw [aaParams_jointTT]
    cases w <;> norm_num [aaParams, aaAlpha, aaBeta, aaRho]

theorem aa_train_tradeProbability :
    correlationEventProbability aaPrior
        (fun w => parameterInferenceLaw (aaParams w) (aaParams_feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (aaTrain1 w) (aaTrain2 w)) =
      3791 / 4000 := by
  simp only [correlationEventProbability, preferredProbability, Fintype.sum_bool,
    Fintype.sum_prod_type]
  rw [(aa_mass_values true).1, (aa_mass_values true).2.1, (aa_mass_values true).2.2.1,
    (aa_mass_values true).2.2.2, (aa_mass_values false).1, (aa_mass_values false).2.1,
    (aa_mass_values false).2.2.1, (aa_mass_values false).2.2.2]
  norm_num [aaPrior, aaTrain1, aaTrain2, TrainSharing.Theorem43.tradeEvent, follow, alwaysAct]

theorem aa_noSharing_tradeProbability :
    correlationEventProbability aaPrior
        (fun w => parameterInferenceLaw (aaParams w) (aaParams_feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent follow follow) =
      1851 / 2000 := by
  simp only [correlationEventProbability, preferredProbability, Fintype.sum_bool,
    Fintype.sum_prod_type]
  rw [(aa_mass_values true).1, (aa_mass_values true).2.1, (aa_mass_values true).2.2.1,
    (aa_mass_values true).2.2.2, (aa_mass_values false).1, (aa_mass_values false).2.1,
    (aa_mass_values false).2.2.1, (aa_mass_values false).2.2.2]
  norm_num [aaPrior, TrainSharing.Theorem43.tradeEvent, follow]

/-! ## The contract-level picture -/

/-- Each contract's selected-equilibrium payoff vector. -/
noncomputable def aaUtility : Contract → Firm → ℝ
  | .noSharing, .firm1 =>
      weightedNoSharingPayoff1 aaAlpha aaBeta aaRhoBar aaReward aaCost follow follow
  | .noSharing, .firm2 =>
      weightedNoSharingPayoff2 aaAlpha aaBeta aaRhoBar aaReward aaCost follow follow
  | .trainSharing, .firm1 =>
      1 / 20 * weightedNoSharingPayoff1 aaAlpha aaBeta (aaRho true) aaReward aaCost
          alwaysAct alwaysAct +
        19 / 20 * weightedNoSharingPayoff1 aaAlpha aaBeta (aaRho false) aaReward aaCost
          follow follow
  | .trainSharing, .firm2 =>
      1 / 20 * weightedNoSharingPayoff2 aaAlpha aaBeta (aaRho true) aaReward aaCost
          alwaysAct alwaysAct +
        19 / 20 * weightedNoSharingPayoff2 aaAlpha aaBeta (aaRho false) aaReward aaCost
          follow follow
  | .fullSharing, _ =>
      1 / 20 * fullInfoPayoff aaAlpha aaBeta (aaRho true) aaReward aaCost +
        19 / 20 * fullInfoPayoff aaAlpha aaBeta (aaRho false) aaReward aaCost
  | .inferSharing, _ => fullInfoPayoff aaAlpha aaBeta aaRhoBar aaReward aaCost

theorem aaUtility_values :
    aaUtility .noSharing .firm1 = 2621 / 32000 ∧
    aaUtility .noSharing .firm2 = 2341 / 32000 ∧
    aaUtility .trainSharing .firm1 = 2627 / 32000 ∧
    aaUtility .trainSharing .firm2 = 2361 / 32000 ∧
    aaUtility .fullSharing .firm1 = 2494 / 32000 ∧
    aaUtility .fullSharing .firm2 = 2494 / 32000 ∧
    aaUtility .inferSharing .firm1 = 2481 / 32000 ∧
    aaUtility .inferSharing .firm2 = 2481 / 32000 := by
  refine ⟨aa_payoff1_noSharing, aa_payoff2_noSharing, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 / 20 * _ + 19 / 20 * _ = _
    rw [aa_payoff1_world_true, aa_payoff1_world_false]; norm_num
  · show 1 / 20 * _ + 19 / 20 * _ = _
    rw [aa_payoff2_world_true, aa_payoff2_world_false]; norm_num
  all_goals
    first
      | (show 1 / 20 * _ + 19 / 20 * _ = _
         rw [aa_fullInfoPayoff_world_true, aa_fullInfoPayoff_world_false]
         norm_num)
      | exact aa_fullInfoPayoff_noSharing

/-- The equilibrium selection of this instance. -/
noncomputable def aaSelection : EquilibriumSelection Bool where
  utility := aaUtility
  event c :=
    match c with
    | .trainSharing => fun w => TrainSharing.Theorem43.tradeEvent (aaTrain1 w) (aaTrain2 w)
    | .noSharing => fun _ => TrainSharing.Theorem43.tradeEvent follow follow
    | .fullSharing => fun _ q => q.1
    | .inferSharing => fun _ q => q.1
  trainFirm1 := aaTrain1
  trainFirm2 := aaTrain2
  noFirm1 := follow
  noFirm2 := follow
  equilibrium_nonnegative := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := aaUtility_values
    intro c i
    cases c <;> cases i <;>
      first
        | (rw [h1]; norm_num) | (rw [h2]; norm_num) | (rw [h3]; norm_num)
        | (rw [h4]; norm_num) | (rw [h5]; norm_num) | (rw [h6]; norm_num)
        | (rw [h7]; norm_num) | (rw [h8]; norm_num)
  train_event := rfl
  no_event := rfl
  inactive_train_utility := by
    intro htrivial
    exact absurd ((htrivial true).1 true) (by decide)

/-- Train sharing is literally the unique IRPO contract of this instance. -/
theorem aa_trainSharing_uniquely_IRPO :
    TrainSharing.Theorem46.Selected.IsUniquelyIRPO aaSelection Contract.trainSharing := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := aaUtility_values
  have hutil : ∀ c i, aaSelection.utility c i = aaUtility c i := fun _ _ => rfl
  constructor
  · constructor
    · refine Or.inr ?_
      intro i
      cases i
      · rw [hutil, hutil, h1, h3]; norm_num
      · rw [hutil, hutil, h2, h4]; norm_num
    · intro d hd
      cases d
      · have := hd.1 Firm.firm1
        rw [hutil, hutil, h1, h3] at this; norm_num at this
      · exact hd.2 hd.1
      · have := hd.1 Firm.firm1
        rw [hutil, hutil, h7, h3] at this; norm_num at this
      · have := hd.1 Firm.firm1
        rw [hutil, hutil, h5, h3] at this; norm_num at this
  · intro d hd
    cases d
    · exfalso
      refine hd.2 Contract.trainSharing ⟨?_, ?_⟩
      · intro i
        cases i
        · rw [hutil, hutil, h1, h3]; norm_num
        · rw [hutil, hutil, h2, h4]; norm_num
      · intro hcon
        have := hcon Firm.firm1
        rw [hutil, hutil, h1, h3] at this; norm_num at this
    · rfl
    · exfalso
      rcases hd.1 with hcon | hdom
      · exact Contract.noConfusion hcon
      · have := hdom Firm.firm1
        rw [hutil, hutil, h1, h7] at this; norm_num at this
    · exfalso
      rcases hd.1 with hcon | hdom
      · exact Contract.noConfusion hcon
      · have := hdom Firm.firm1
        rw [hutil, hutil, h1, h5] at this; norm_num at this

/-- The selection has the model's payoffs, and its no-sharing game is played at the prior
mixture of the two correlation cells. -/
theorem aa_modelPayoffs :
    Parts.ModelPayoffs aaSelection aaPrior aaParams aaAlpha aaBeta aaRhoBar aaReward
      aaCost := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · simp only [Fintype.sum_bool, aaParams_jointTT]
    norm_num [aaPrior, aaRho, aaRhoBar]
  · show aaUtility Contract.trainSharing Firm.firm1 = _
    simp only [Fintype.sum_bool, aaParams_jointTT]
    norm_num [aaUtility, aaPrior, aaSelection, aaTrain1, aaTrain2]
  · show aaUtility Contract.trainSharing Firm.firm2 = _
    simp only [Fintype.sum_bool, aaParams_jointTT]
    norm_num [aaUtility, aaPrior, aaSelection, aaTrain1, aaTrain2]

/-! ## The refutation of the selected reading -/

/-- **With an all-acting world, the selected reading of Theorem 4.6(1) fails.**

Every hypothesis of `Part1.theorem4_6_part1_nonInverted` holds at this instance
*except* the requirement that no world be all-acting: train sharing is literally the unique
IRPO contract, the payoffs are the model's, the no-sharing game is played at the prior
mixture, all three profiles are strict equilibria, and the train-sharing equilibrium is
not inverted — the secondary firm never acts after `b` without also acting after `a`.
There is one
all-acting world, and the conclusion fails: the opportunity-seeking consumer strictly
prefers train sharing. -/
theorem theorem4_6_part1_allActing_selected_fails :
    TrainSharing.Theorem46.Selected.IsUniquelyIRPO aaSelection Contract.trainSharing ∧
    Parts.ModelPayoffs aaSelection aaPrior aaParams aaAlpha aaBeta aaRhoBar aaReward aaCost ∧
    (1 / 2 ≤ aaAlpha ∧ 1 / 2 ≤ aaBeta ∧ aaBeta ≤ aaAlpha ∧ 0 ≤ aaReward ∧ 0 ≤ aaCost) ∧
    (∀ w, (aaParams w).alpha = aaAlpha) ∧ (∀ w, (aaParams w).beta = aaBeta) ∧
    IsStrictWeightedNash aaAlpha aaBeta aaRhoBar aaReward aaCost aaSelection.noFirm1
      aaSelection.noFirm2 ∧
    (∀ w, IsStrictWeightedNash aaAlpha aaBeta ((aaParams w).jointTT) aaReward aaCost
      (aaSelection.trainFirm1 w) (aaSelection.trainFirm2 w)) ∧
    Selected.NonInverted aaSelection.trainFirm2 ∧
    (∃ w, aaSelection.trainFirm1 w false = true) ∧
    ¬ (correlationEventProbability aaPrior
        (fun w => parameterInferenceLaw (aaParams w) (aaParams_feasible w))
        (aaSelection.event .trainSharing) ≤
      correlationEventProbability aaPrior
        (fun w => parameterInferenceLaw (aaParams w) (aaParams_feasible w))
        (aaSelection.event .noSharing)) := by
  refine ⟨aa_trainSharing_uniquely_IRPO, aa_modelPayoffs, ⟨by norm_num [aaAlpha],
    by norm_num [aaBeta], by norm_num [aaAlpha, aaBeta], by norm_num [aaReward],
    by norm_num [aaCost]⟩, fun _ => rfl, fun _ => rfl, aa_equilibrium_noSharing, ?_,
    ?_, ⟨true, rfl⟩, ?_⟩
  · intro w
    rw [aaParams_jointTT]
    cases w
    · exact aa_equilibrium_world_false
    · exact aa_equilibrium_world_true
  · intro w _
    cases w <;> rfl
  · show ¬ (correlationEventProbability aaPrior _
      (fun w => TrainSharing.Theorem43.tradeEvent (aaTrain1 w) (aaTrain2 w)) ≤
      correlationEventProbability aaPrior _
        (fun _ => TrainSharing.Theorem43.tradeEvent follow follow))
    rw [aa_train_tradeProbability, aa_noSharing_tradeProbability]
    norm_num

/-- **…but the existential reading survives**, on the very same instance: the all-acting
profile is a strict equilibrium of the no-sharing game at the prior mixture, and it trades
with probability one, so the consumer weakly prefers *it*.  This is
`Part1.theorem4_6_part1_existence_nonInverted` specialized to the instance. -/
theorem aa_existence_conclusion_holds :
    ∃ n1 n2 : Bool → Bool,
      IsStrictWeightedNash aaAlpha aaBeta aaRhoBar aaReward aaCost n1 n2 ∧
      correlationEventProbability aaPrior
          (fun w => parameterInferenceLaw (aaParams w) (aaParams_feasible w))
          (aaSelection.event .trainSharing) ≤
        correlationEventProbability aaPrior
          (fun w => parameterInferenceLaw (aaParams w) (aaParams_feasible w))
          (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
  obtain ⟨hunique, hmodel, ⟨ha, hb, hab, hr, hc⟩, halphaw, hbetaw, hno, htrain, hnonInverted, _, _⟩ :=
    theorem4_6_part1_allActing_selected_fails
  exact Part1.theorem4_6_part1_existence_nonInverted aaPrior aaParams
    aaParams_feasible aaSelection aaAlpha aaBeta aaRhoBar aaReward aaCost hunique hmodel
    ha hb hab hr hc halphaw hbetaw hno htrain hnonInverted

end TrainSharing.Theorem46.AllActing
