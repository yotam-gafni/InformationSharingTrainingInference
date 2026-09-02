import RequestProject.Theorem46Part1NonInverted

/-!
# Example 4.7: an inverted train-sharing equilibrium

Theorem 4.6 assumes that the train-sharing equilibrium is *not inverted* (Definition 4.5):
in no correlation world does the secondary firm take the significant action after its
negative inference signal and not after its positive one.  This file verifies the
manuscript's Example 4.7, which shows that the assumption cannot be dropped: at an
inverted equilibrium the opportunity-seeking consumer may strictly prefer train sharing to
*every* equilibrium of the no-sharing game.

## The instance

Accuracies `alpha = 3/4` and `beta = 101/200`, reward `R₁ = 1`, mistake cost
`C₁ = 143/200`, and two correlation worlds:

* world `w₁` (prior `1/3`) with joint positive cell `rho₁ = 13/50`;
* world `w₂` (prior `2/3`) with joint positive cell `rho₂ = 1/2`.

Both lie strictly inside the Fréchet interval `[51/200, 101/200]`, so both are feasible
correlations of the model, and the no-sharing game is played against the mixture
`rho̅ = 21/50`.

## What happens

In each of the three games the pure equilibrium is unique:

* world `w₁`: both firms follow their inference signals;
* world `w₂`: Firm 1 follows its signal, while Firm 2 acts **on its negative signal
  only** — the inverted pattern.  In the strongly correlated world, Firm 2's positive
  signal `a` is precisely the event on which Firm 1 also acts and takes half the market,
  whereas after `b` it is likely to have the market to itself;
* no sharing: both firms follow their inference signals.

Train sharing strictly Pareto dominates no sharing, and neither full sharing nor
inference sharing is individually rational against no sharing, so train sharing is
literally the unique IRPO contract.  Nevertheless the consumer strictly prefers train
sharing: it trades with probability `209/240 ≈ 0.871`, against `283/400 = 0.7075` for the
unique no-sharing equilibrium — the numbers printed in the manuscript.

The last three results record what this means for Theorem 4.6(1):
`example4_7_refutes_part1` collects every hypothesis of the theorem except non-inversion,
`ex47_no_noSharing_equilibrium_is_preferred` shows that the conclusion fails even in its
weakest, existential reading, and `nonInverted_hypothesis_is_necessary` states that the
only hypothesis this instance violates is non-inversion itself.
-/

namespace TrainSharing.Theorem46.Example47

open TrainSharing
open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric
open TrainSharing.Theorem43
open TrainSharing.Theorem46
open TrainSharing.Theorem46.Selected
open TrainSharing.Theorem46.Upper
open TrainSharing.Theorem46.Parts

/-! ## The instance -/

/-- Firm 1's accuracy. -/
noncomputable def ex47Alpha : ℝ := 3 / 4
/-- Firm 2's accuracy: barely better than a coin flip. -/
noncomputable def ex47Beta : ℝ := 101 / 200
/-- Reward for a correct significant action. -/
noncomputable def ex47Reward : ℝ := 1
/-- Cost of an incorrect significant action. -/
noncomputable def ex47Cost : ℝ := 143 / 200
/-- The two correlation worlds, indexed by `Bool`. -/
noncomputable def ex47Rho : Bool → ℝ := fun w => if w then 13 / 50 else 1 / 2
/-- The mixture correlation seen under no sharing. -/
noncomputable def ex47RhoBar : ℝ := 21 / 50

/-- The selected train-sharing strategy of Firm 1: follow the signal in every world. -/
def ex47Train1 : Bool → Bool → Bool := fun _ => follow
/-- The selected train-sharing strategy of Firm 2. -/
def ex47Train2 : Bool → Bool → Bool := fun w => if w then follow else antiFollow

/-- The prior over the two correlation worlds. -/
noncomputable def ex47Prior : FiniteLaw Bool where
  mass w := if w then 1 / 3 else 2 / 3
  nonneg w := by cases w <;> norm_num
  total := by norm_num [Fintype.sum_bool]

/-! ### Signs of the four scores in the three games -/

theorem ex47_scores_world_true :
    0 < weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost true true ∧
    0 < weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost true false ∧
    weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost false true < 0 ∧
    weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost false false < 0 := by
  norm_num [weightedSharedScore, conditionalMass, ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho]

theorem ex47_scores_world_false :
    0 < weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost true true ∧
    0 < weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost true false ∧
    weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost false true < 0 ∧
    weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost false false < 0 := by
  norm_num [weightedSharedScore, conditionalMass, ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho]

theorem ex47_scores_noSharing :
    0 < weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost true true ∧
    0 < weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost true false ∧
    weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost false true < 0 ∧
    weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost false false < 0 := by
  norm_num [weightedSharedScore, conditionalMass, ex47Alpha, ex47Beta, ex47Reward, ex47Cost,
    ex47RhoBar]

/-- Firm 2's incentives in world `w₁`: it follows its signal. -/
theorem ex47_firm2_world_true :
    0 < weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost true true / 2 +
      weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost false true ∧
    weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost true false / 2 +
      weightedSharedScore ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost false false < 0 := by
  norm_num [weightedSharedScore, conditionalMass, ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho]

/-- Firm 2's incentives in world `w₂`: it acts on its *negative* signal only. -/
theorem ex47_firm2_world_false :
    weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost true true / 2 +
      weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost false true < 0 ∧
    0 < weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost true false / 2 +
      weightedSharedScore ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost false false := by
  norm_num [weightedSharedScore, conditionalMass, ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho]

/-- Firm 2's incentives under no sharing: it follows its signal. -/
theorem ex47_firm2_noSharing :
    0 < weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost true true / 2 +
      weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost false true ∧
    weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost true false / 2 +
      weightedSharedScore ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost false false < 0 := by
  norm_num [weightedSharedScore, conditionalMass, ex47Alpha, ex47Beta, ex47Reward, ex47Cost,
    ex47RhoBar]

/-! ### The three games have unique pure equilibria -/

theorem ex47_unique_world_true (s1 s2 : Bool → Bool)
    (hnash : IsWeightedNoSharingNash ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost s1 s2) :
    s1 = follow ∧ s2 = follow := by
  obtain ⟨hAt, hAf, hBt, hBf⟩ := ex47_scores_world_true
  have hs1 : s1 = follow := firm1_eq_follow _ _ _ _ _ _ _ hAt hAf hBt hBf hnash
  refine ⟨hs1, ?_⟩
  obtain ⟨ha, hb⟩ := ex47_firm2_world_true
  funext y
  cases y with
  | true => simpa [follow] using firm2_act_of_pos _ _ _ _ _ _ _ true hs1 ha hnash
  | false => simpa [follow] using firm2_out_of_neg _ _ _ _ _ _ _ false hs1 hb hnash

theorem ex47_unique_world_false (s1 s2 : Bool → Bool)
    (hnash : IsWeightedNoSharingNash ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost s1 s2) :
    s1 = follow ∧ s2 = antiFollow := by
  obtain ⟨hAt, hAf, hBt, hBf⟩ := ex47_scores_world_false
  have hs1 : s1 = follow := firm1_eq_follow _ _ _ _ _ _ _ hAt hAf hBt hBf hnash
  refine ⟨hs1, ?_⟩
  obtain ⟨ha, hb⟩ := ex47_firm2_world_false
  funext y
  cases y with
  | true => simpa [antiFollow] using firm2_out_of_neg _ _ _ _ _ _ _ true hs1 ha hnash
  | false => simpa [antiFollow] using firm2_act_of_pos _ _ _ _ _ _ _ false hs1 hb hnash

theorem ex47_unique_noSharing (s1 s2 : Bool → Bool)
    (hnash : IsWeightedNoSharingNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost s1 s2) :
    s1 = follow ∧ s2 = follow := by
  obtain ⟨hAt, hAf, hBt, hBf⟩ := ex47_scores_noSharing
  have hs1 : s1 = follow := firm1_eq_follow _ _ _ _ _ _ _ hAt hAf hBt hBf hnash
  refine ⟨hs1, ?_⟩
  obtain ⟨ha, hb⟩ := ex47_firm2_noSharing
  funext y
  cases y with
  | true => simpa [follow] using firm2_act_of_pos _ _ _ _ _ _ _ true hs1 ha hnash
  | false => simpa [follow] using firm2_out_of_neg _ _ _ _ _ _ _ false hs1 hb hnash

/-! ### The stated profiles really are (strict) equilibria -/

theorem ex47_equilibrium_world_true :
    IsStrictWeightedNash ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost follow follow := by
  constructor <;> intro x <;> cases x <;>
    norm_num [weightedFirm1Gain, weightedFirm2Gain, conditionalMass, follow, shareFactor,
      ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho]

theorem ex47_equilibrium_world_false :
    IsStrictWeightedNash ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost follow antiFollow := by
  constructor <;> intro x <;> cases x <;>
    norm_num [weightedFirm1Gain, weightedFirm2Gain, conditionalMass, follow, antiFollow,
      shareFactor, ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho]

theorem ex47_equilibrium_noSharing :
    IsStrictWeightedNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost follow follow := by
  constructor <;> intro x <;> cases x <;>
    norm_num [weightedFirm1Gain, weightedFirm2Gain, conditionalMass, follow, shareFactor,
      ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47RhoBar]

/-! ### Equilibrium payoffs -/

theorem ex47_payoff1_world_true :
    weightedNoSharingPayoff1 ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost follow follow =
      35443 / 160000 := by
  norm_num [weightedNoSharingPayoff1, conditionalMass, follow, shareFactor,
    ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho, Fintype.sum_prod_type]

theorem ex47_payoff2_world_true :
    weightedNoSharingPayoff2 ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost follow follow =
      1829 / 160000 := by
  norm_num [weightedNoSharingPayoff2, conditionalMass, follow, shareFactor,
    ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho, Fintype.sum_prod_type]

theorem ex47_payoff1_world_false :
    weightedNoSharingPayoff1 ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost follow antiFollow =
      35843 / 160000 := by
  norm_num [weightedNoSharingPayoff1, conditionalMass, follow, antiFollow, shareFactor,
    ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho, Fintype.sum_prod_type]

theorem ex47_payoff2_world_false :
    weightedNoSharingPayoff2 ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost follow antiFollow =
      857 / 160000 := by
  norm_num [weightedNoSharingPayoff2, conditionalMass, follow, antiFollow, shareFactor,
    ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho, Fintype.sum_prod_type]

theorem ex47_payoff1_noSharing :
    weightedNoSharingPayoff1 ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost follow follow =
      33619 / 160000 := by
  norm_num [weightedNoSharingPayoff1, conditionalMass, follow, shareFactor,
    ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47RhoBar, Fintype.sum_prod_type]

theorem ex47_payoff2_noSharing :
    weightedNoSharingPayoff2 ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost follow follow =
      1 / 32000 := by
  norm_num [weightedNoSharingPayoff2, conditionalMass, follow, shareFactor,
    ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47RhoBar, Fintype.sum_prod_type]

theorem ex47_fullInfoPayoff (rho : ℝ) (h : rho = ex47Rho true ∨ rho = ex47Rho false ∨ rho = ex47RhoBar) :
    fullInfoPayoff ex47Alpha ex47Beta rho ex47Reward ex47Cost = 457 / 3200 := by
  rcases h with h | h | h <;> subst h <;>
    norm_num [fullInfoPayoff, weightedSharedScore, conditionalMass,
      ex47Alpha, ex47Beta, ex47Reward, ex47Cost, ex47Rho, ex47RhoBar, Fintype.sum_prod_type]

/-! ### The correlation parameters of the two worlds -/

/-- The two feasible correlation worlds, presented as parameters of the Section 3 model.
`theta` is chosen so that the joint positive cell is exactly `ex47Rho w`. -/
noncomputable def ex47Params (w : Bool) : TrainSharing.Correlation.Parameters where
  alpha := ex47Alpha
  beta := ex47Beta
  theta := (ex47Rho w - ex47Alpha * ex47Beta) /
    Real.sqrt (ex47Alpha * (1 - ex47Alpha) * ex47Beta * (1 - ex47Beta))
  alpha_mem := by constructor <;> norm_num [ex47Alpha]
  beta_mem := by constructor <;> norm_num [ex47Beta]

theorem ex47Params_jointTT (w : Bool) : (ex47Params w).jointTT = ex47Rho w := by
  have hs := TrainSharing.Correlation.Parameters.scale_pos (ex47Params w)
  show ex47Alpha * ex47Beta + ((ex47Rho w - ex47Alpha * ex47Beta) /
    Real.sqrt (ex47Alpha * (1 - ex47Alpha) * ex47Beta * (1 - ex47Beta))) * (ex47Params w).scale =
      ex47Rho w
  have hscale : (ex47Params w).scale =
      Real.sqrt (ex47Alpha * (1 - ex47Alpha) * ex47Beta * (1 - ex47Beta)) := rfl
  rw [hscale] at hs ⊢
  rw [div_mul_cancel₀ _ (ne_of_gt hs)]
  ring

theorem ex47Params_feasible (w : Bool) : (ex47Params w).Feasible := by
  constructor <;> rw [ex47Params_jointTT w] <;> cases w <;>
    simp [ex47Params, ex47Alpha, ex47Beta, ex47Rho] <;> norm_num

/-! ### Consumer trade probabilities -/

/-- The unconditional inference law of a world is the average of the two label-conditional
signal laws. -/
theorem ex47_mass (w : Bool) (q : Bool × Bool) :
    (parameterInferenceLaw (ex47Params w) (ex47Params_feasible w)).mass q =
      ((ex47Params w).jointMass q + (ex47Params w).jointMass (!q.1, !q.2)) / 2 := by
  simp [parameterInferenceLaw, TrainSharing.Correlation.Parameters.world,
    TrainSharing.Correlation.Parameters.signalLaw]
  ring

theorem ex47_mass_values (w : Bool) :
    (parameterInferenceLaw (ex47Params w) (ex47Params_feasible w)).mass (true, true) =
      (if w then 53 else 149) / 400 ∧
    (parameterInferenceLaw (ex47Params w) (ex47Params_feasible w)).mass (true, false) =
      (if w then 147 else 51) / 400 ∧
    (parameterInferenceLaw (ex47Params w) (ex47Params_feasible w)).mass (false, true) =
      (if w then 147 else 51) / 400 ∧
    (parameterInferenceLaw (ex47Params w) (ex47Params_feasible w)).mass (false, false) =
      (if w then 53 else 149) / 400 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [ex47_mass]
    simp only [TrainSharing.Correlation.Parameters.jointMass, Bool.not_true, Bool.not_false]
    rw [ex47Params_jointTT]
    cases w <;> norm_num [ex47Params, ex47Alpha, ex47Beta, ex47Rho]

theorem ex47_train_tradeProbability :
    correlationEventProbability ex47Prior
        (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
        (fun w => TrainSharing.Theorem43.tradeEvent (ex47Train1 w) (ex47Train2 w)) =
      209 / 240 := by
  simp only [correlationEventProbability, preferredProbability, Fintype.sum_bool,
    Fintype.sum_prod_type]
  rw [(ex47_mass_values true).1, (ex47_mass_values true).2.1, (ex47_mass_values true).2.2.1,
    (ex47_mass_values true).2.2.2, (ex47_mass_values false).1, (ex47_mass_values false).2.1,
    (ex47_mass_values false).2.2.1, (ex47_mass_values false).2.2.2]
  norm_num [ex47Prior, ex47Train1, ex47Train2, TrainSharing.Theorem43.tradeEvent, follow,
    antiFollow]

theorem ex47_noSharing_tradeProbability :
    correlationEventProbability ex47Prior
        (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
        (fun _ => TrainSharing.Theorem43.tradeEvent follow follow) =
      283 / 400 := by
  simp only [correlationEventProbability, preferredProbability, Fintype.sum_bool,
    Fintype.sum_prod_type]
  rw [(ex47_mass_values true).1, (ex47_mass_values true).2.1, (ex47_mass_values true).2.2.1,
    (ex47_mass_values true).2.2.2, (ex47_mass_values false).1, (ex47_mass_values false).2.1,
    (ex47_mass_values false).2.2.1, (ex47_mass_values false).2.2.2]
  norm_num [ex47Prior, TrainSharing.Theorem43.tradeEvent, follow]

/-! ## The contract-level picture: train sharing is the unique IRPO contract -/

/-- Each contract's selected-equilibrium payoff vector.  Train sharing plays the unique
equilibrium of each revealed world; no sharing plays the unique equilibrium of the mixture
game; full sharing and inference sharing play their (dominant-action) full-information
equilibria. -/
noncomputable def ex47Utility : Contract → Firm → ℝ
  | .noSharing, .firm1 =>
      weightedNoSharingPayoff1 ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost follow follow
  | .noSharing, .firm2 =>
      weightedNoSharingPayoff2 ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost follow follow
  | .trainSharing, .firm1 =>
      1 / 3 * weightedNoSharingPayoff1 ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost
          follow follow +
        2 / 3 * weightedNoSharingPayoff1 ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost
          follow antiFollow
  | .trainSharing, .firm2 =>
      1 / 3 * weightedNoSharingPayoff2 ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost
          follow follow +
        2 / 3 * weightedNoSharingPayoff2 ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost
          follow antiFollow
  | .fullSharing, _ =>
      1 / 3 * fullInfoPayoff ex47Alpha ex47Beta (ex47Rho true) ex47Reward ex47Cost +
        2 / 3 * fullInfoPayoff ex47Alpha ex47Beta (ex47Rho false) ex47Reward ex47Cost
  | .inferSharing, _ => fullInfoPayoff ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost

theorem ex47Utility_values :
    ex47Utility .noSharing .firm1 = 33619 / 160000 ∧
    ex47Utility .noSharing .firm2 = 1 / 32000 ∧
    ex47Utility .trainSharing .firm1 = 107129 / 480000 ∧
    ex47Utility .trainSharing .firm2 = 1181 / 160000 ∧
    ex47Utility .fullSharing .firm1 = 457 / 3200 ∧
    ex47Utility .fullSharing .firm2 = 457 / 3200 ∧
    ex47Utility .inferSharing .firm1 = 457 / 3200 ∧
    ex47Utility .inferSharing .firm2 = 457 / 3200 := by
  refine ⟨ex47_payoff1_noSharing, ex47_payoff2_noSharing, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 / 3 * _ + 2 / 3 * _ = _
    rw [ex47_payoff1_world_true, ex47_payoff1_world_false]; norm_num
  · show 1 / 3 * _ + 2 / 3 * _ = _
    rw [ex47_payoff2_world_true, ex47_payoff2_world_false]; norm_num
  all_goals
    first
      | (show 1 / 3 * _ + 2 / 3 * _ = _
         rw [ex47_fullInfoPayoff _ (Or.inl rfl), ex47_fullInfoPayoff _ (Or.inr (Or.inl rfl))]
         norm_num)
      | exact ex47_fullInfoPayoff _ (Or.inr (Or.inr rfl))

/-- The equilibrium selection of Example 4.7, in the interface of
`Theorem46Selected.lean`. -/
noncomputable def ex47Selection : EquilibriumSelection Bool where
  utility := ex47Utility
  event c :=
    match c with
    | .trainSharing => fun w => TrainSharing.Theorem43.tradeEvent (ex47Train1 w) (ex47Train2 w)
    | .noSharing => fun _ => TrainSharing.Theorem43.tradeEvent follow follow
    | .fullSharing => fun _ q => q.1
    | .inferSharing => fun _ q => q.1
  trainFirm1 := ex47Train1
  trainFirm2 := ex47Train2
  noFirm1 := follow
  noFirm2 := follow
  equilibrium_nonnegative := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ex47Utility_values
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

/-- Train sharing is literally the unique IRPO contract of Example 4.7: it strictly
Pareto dominates no sharing, nothing dominates it, and neither full sharing nor inference
sharing is individually rational against no sharing. -/
theorem ex47_trainSharing_uniquely_IRPO :
    TrainSharing.Theorem46.Selected.IsUniquelyIRPO ex47Selection Contract.trainSharing := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ex47Utility_values
  have hutil : ∀ c i, ex47Selection.utility c i = ex47Utility c i := fun _ _ => rfl
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

/-! ## The refutation of Theorem 4.6(1) -/

/-- **Theorem 4.6(1) fails in the manuscript's own model.**

All the hypotheses of Theorem 4.6 hold at this instance: significant-action utilities with
`R₁ = 1`, `C₁ = 143/200`, accuracies `3/4 ≥ 101/200 ≥ 1/2`, a two-point distribution over
feasible correlations, and train sharing literally the unique IRPO contract.  Each of the
three relevant games has exactly one pure equilibrium, and each of these is strict.  Yet
the normalized opportunity-seeking consumer strictly prefers train sharing to the (unique)
no-sharing equilibrium.

The manuscript's argument breaks at the sentence “After eliminating this option, for any
correlation, the train-sharing equilibrium is not more conducive for trade than
no-sharing”.  In the strongly correlated world Firm 2 acts on its *negative* inference
signal and stays out after its positive one: acting after `a` would mean acting exactly
where Firm 1 also acts and takes half the market.  Such non-monotone behaviour is exactly
what the accompanying monotonicity claim (“if the weaker signal leads to a significant
action, then so should the stronger”) excludes, and it is not available in this model. -/
theorem example4_7_consumer_prefers_trainSharing :
    TrainSharing.Theorem46.Selected.IsUniquelyIRPO ex47Selection Contract.trainSharing ∧
    (∀ w, IsStrictWeightedNash ex47Alpha ex47Beta (ex47Rho w) ex47Reward ex47Cost
      (ex47Selection.trainFirm1 w) (ex47Selection.trainFirm2 w)) ∧
    (∀ w s1 s2, IsWeightedNoSharingNash ex47Alpha ex47Beta (ex47Rho w) ex47Reward ex47Cost s1 s2 →
      s1 = ex47Selection.trainFirm1 w ∧ s2 = ex47Selection.trainFirm2 w) ∧
    IsStrictWeightedNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost
      ex47Selection.noFirm1 ex47Selection.noFirm2 ∧
    (∀ s1 s2, IsWeightedNoSharingNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost s1 s2 →
      s1 = ex47Selection.noFirm1 ∧ s2 = ex47Selection.noFirm2) ∧
    correlationEventProbability ex47Prior
        (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
        (ex47Selection.event .noSharing) <
      correlationEventProbability ex47Prior
        (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
        (ex47Selection.event .trainSharing) := by
  refine ⟨ex47_trainSharing_uniquely_IRPO, ?_, ?_, ex47_equilibrium_noSharing,
    ex47_unique_noSharing, ?_⟩
  · intro w
    cases w
    · exact ex47_equilibrium_world_false
    · exact ex47_equilibrium_world_true
  · intro w s1 s2 h
    cases w
    · exact ex47_unique_world_false s1 s2 h
    · exact ex47_unique_world_true s1 s2 h
  · show correlationEventProbability ex47Prior _
        (fun _ => TrainSharing.Theorem43.tradeEvent follow follow) <
      correlationEventProbability ex47Prior _
        (fun w => TrainSharing.Theorem43.tradeEvent (ex47Train1 w) (ex47Train2 w))
    rw [ex47_noSharing_tradeProbability, ex47_train_tradeProbability]
    norm_num

/-- Consequently the transfer premise of `ManuscriptEquilibriumConsequences` is not a
consequence of the manuscript's hypotheses: it fails at this instance, even though train
sharing is literally uniquely IRPO.  (Its companion premise, worldwise activity, *is*
derivable; see `Theorem46UpperBound.lean`.) -/
theorem ex47_manuscriptEquilibriumConsequences_fails :
    ¬ ManuscriptEquilibriumConsequences ex47Selection := by
  intro h
  have hle : correlationEventProbability ex47Prior
      (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
      (ex47Selection.event .trainSharing) ≤
    correlationEventProbability ex47Prior
      (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
      (ex47Selection.event .noSharing) := by
    unfold correlationEventProbability
    refine Finset.sum_le_sum fun w _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (ex47Prior.nonneg w)
    exact theorem4_3_part1_of_pointwise_permissive _ _ _ (h.noSharingTransfer w)
  have := example4_7_consumer_prefers_trainSharing.2.2.2.2.2
  linarith

/-! ## Consequences for Theorem 4.6(1) -/

/-- The selection of Example 4.7 has the model's payoffs, and its no-sharing game is
played at the prior mixture of the two correlation cells. -/
theorem ex47_modelPayoffs :
    ModelPayoffs ex47Selection ex47Prior ex47Params ex47Alpha ex47Beta ex47RhoBar ex47Reward
      ex47Cost := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · simp only [Fintype.sum_bool, ex47Params_jointTT]
    norm_num [ex47Prior, ex47Rho, ex47RhoBar]
  · show ex47Utility Contract.trainSharing Firm.firm1 = _
    simp only [Fintype.sum_bool, ex47Params_jointTT]
    norm_num [ex47Utility, ex47Prior, ex47Selection, ex47Train1, ex47Train2]
  · show ex47Utility Contract.trainSharing Firm.firm2 = _
    simp only [Fintype.sum_bool, ex47Params_jointTT]
    norm_num [ex47Utility, ex47Prior, ex47Selection, ex47Train1, ex47Train2]

/-- **The non-inversion hypothesis of Theorem 4.6(1) is necessary.**

Every hypothesis of `theorem4_6_part1_nonInverted` except non-inversion holds at this
instance, its no-sharing equilibrium is the unique equilibrium of the mixture game, the
selected train-sharing equilibrium is inverted, and the conclusion fails: the
opportunity-seeking consumer strictly prefers train sharing. -/
theorem example4_7_refutes_part1 :
    TrainSharing.Theorem46.Selected.IsUniquelyIRPO ex47Selection Contract.trainSharing ∧
    ModelPayoffs ex47Selection ex47Prior ex47Params ex47Alpha ex47Beta ex47RhoBar ex47Reward
      ex47Cost ∧
    (1 / 2 ≤ ex47Alpha ∧ 1 / 2 ≤ ex47Beta ∧ ex47Beta ≤ ex47Alpha ∧ 0 ≤ ex47Reward ∧
      0 ≤ ex47Cost) ∧
    (∀ w, (ex47Params w).alpha = ex47Alpha) ∧ (∀ w, (ex47Params w).beta = ex47Beta) ∧
    IsStrictWeightedNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost
      ex47Selection.noFirm1 ex47Selection.noFirm2 ∧
    (∀ w, IsStrictWeightedNash ex47Alpha ex47Beta ((ex47Params w).jointTT) ex47Reward ex47Cost
      (ex47Selection.trainFirm1 w) (ex47Selection.trainFirm2 w)) ∧
    (∀ s1 s2, IsWeightedNoSharingNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost s1 s2 →
      s1 = ex47Selection.noFirm1 ∧ s2 = ex47Selection.noFirm2) ∧
    Inverted ex47Selection.trainFirm2 ∧
    ¬ (correlationEventProbability ex47Prior
        (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
        (ex47Selection.event .trainSharing) ≤
      correlationEventProbability ex47Prior
        (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
        (ex47Selection.event .noSharing)) := by
  obtain ⟨hunique, hworlds, _, hno, huniqueNo, hstrict⟩ := example4_7_consumer_prefers_trainSharing
  refine ⟨hunique, ex47_modelPayoffs, ⟨by norm_num [ex47Alpha], by norm_num [ex47Beta],
    by norm_num [ex47Alpha, ex47Beta], by norm_num [ex47Reward], by norm_num [ex47Cost]⟩,
    fun _ => rfl, fun _ => rfl, hno, ?_, huniqueNo, ⟨false, rfl, rfl⟩, ?_⟩
  · intro w
    rw [ex47Params_jointTT]
    exact hworlds w
  · intro hle
    exact absurd hstrict (not_lt.mpr hle)

/-- **No no-sharing equilibrium at all is weakly preferred.**  The mixture game of this
instance has exactly one equilibrium, and the consumer strictly prefers train
sharing to it.  So conclusion (1) of Theorem 4.6 fails in its weakest, existential
reading as well: there is no no-sharing equilibrium that the consumer weakly prefers. -/
theorem ex47_no_noSharing_equilibrium_is_preferred :
    ¬ ∃ n1 n2 : Bool → Bool,
      IsWeightedNoSharingNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost n1 n2 ∧
      correlationEventProbability ex47Prior
          (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
          (ex47Selection.event .trainSharing) ≤
        correlationEventProbability ex47Prior
          (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
          (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) := by
  rintro ⟨n1, n2, hnash, hle⟩
  obtain ⟨h1, h2⟩ := ex47_unique_noSharing n1 n2 hnash
  subst h1
  subst h2
  have hstrict := example4_7_consumer_prefers_trainSharing.2.2.2.2.2
  rw [show (ex47Selection.event Contract.noSharing) =
      (fun _ : Bool => TrainSharing.Theorem43.tradeEvent follow follow) from rfl] at hstrict
  exact absurd hstrict (not_lt.mpr hle)

/-- **Non-inversion is exactly what has to be assumed.**

At this instance no world is all-acting and every other hypothesis of
`theorem4_6_part1_existence_nonInverted` holds; the one hypothesis that fails is
non-inversion, since in the strongly correlated world the secondary firm acts after `b`
and not after `a`.  There, no equilibrium of the no-sharing game at the prior mixture is
weakly preferred by the consumer, so conclusion (1) fails in its weakest reading. -/
theorem nonInverted_hypothesis_is_necessary :
    Inverted ex47Selection.trainFirm2 ∧
    (∀ w, ex47Selection.trainFirm1 w false = false) ∧
    ¬ ∃ n1 n2 : Bool → Bool,
      IsWeightedNoSharingNash ex47Alpha ex47Beta ex47RhoBar ex47Reward ex47Cost n1 n2 ∧
      correlationEventProbability ex47Prior
          (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
          (ex47Selection.event .trainSharing) ≤
        correlationEventProbability ex47Prior
          (fun w => parameterInferenceLaw (ex47Params w) (ex47Params_feasible w))
          (fun _ => TrainSharing.Theorem43.tradeEvent n1 n2) :=
  ⟨⟨false, rfl, rfl⟩, fun _ => rfl,
    ex47_no_noSharing_equilibrium_is_preferred⟩

end TrainSharing.Theorem46.Example47
