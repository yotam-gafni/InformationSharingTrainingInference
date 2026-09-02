import RequestProject.BayesianGame

/-!
# The two-hypotheses model (Section 5.1)

This file gives an exact finite presentation of Figure 4 and isolates the scalar
calculations in the proof of Theorem 5.1.  `true` denotes signals `A` and `a`;
`false` denotes `B` and `b`.
-/

namespace TrainSharing

inductive Hypothesis where
  | I | II
  deriving DecidableEq, Fintype, Repr

/-- Parameters `(π_I, κ, λ, μ)` of the two-hypotheses model. -/
structure TwoHypothesesParameters where
  priorI : ℝ
  incidence : ℝ
  mutationNoise : ℝ
  environmentNoise : ℝ

namespace TwoHypothesesParameters

abbrev p (x : TwoHypothesesParameters) := x.priorI
abbrev k (x : TwoHypothesesParameters) := x.incidence
abbrev l (x : TwoHypothesesParameters) := x.mutationNoise
abbrev m (x : TwoHypothesesParameters) := x.environmentNoise

/-- The broad feasibility conditions needed to define the probability model. -/
def Feasible (x : TwoHypothesesParameters) : Prop :=
  0 ≤ x.p ∧ x.p ≤ 1 ∧ 0 ≤ x.k ∧ x.k ≤ 1 ∧
  0 ≤ x.l ∧ 0 ≤ x.m ∧ x.l + x.m ≤ 1

/-- The open parameter box displayed at the end of the proof of Theorem 5.1. -/
def InTheorem51Box (x : TwoHypothesesParameters) : Prop :=
  0 < x.p ∧ x.p < 2 / 15 ∧
  1 / 12 < x.k ∧ x.k < 1 / 6 ∧
  0 < x.l ∧ x.l < 1 / 11 ∧
  1 / 5 < x.m ∧ x.m < 1 / 2

lemma theorem51Box_feasible (x : TwoHypothesesParameters)
    (hx : x.InTheorem51Box) : x.Feasible := by
  unfold InTheorem51Box at hx
  unfold Feasible
  obtain ⟨hp0, hp1, hk0, hk1, hl0, hl1, hm0, hm1⟩ := hx
  refine ⟨le_of_lt hp0, ?_, le_of_lt (by linarith : 0 < x.k), ?_, le_of_lt hl0, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- Prior probability of a hypothesis. -/
def hypothesisMass (x : TwoHypothesesParameters) : Hypothesis → ℝ
  | .I => x.p
  | .II => 1 - x.p

/-- Joint mass of `(label, primary signal, secondary signal)` in Figure 4.
In world I, positive labels produce `Aa`; in world II they produce `Ba`.
For a negative label, the exceptional intervals have lengths `λ` and `μ`. -/
def inferenceMass (x : TwoHypothesesParameters) :
    Hypothesis → InferenceOutcome → ℝ
  | .I, (true, true, true) => x.k
  | .I, (false, true, false) => (1 - x.k) * x.l
  | .I, (false, false, true) => (1 - x.k) * x.m
  | .I, (false, false, false) => (1 - x.k) * (1 - x.l - x.m)
  | .II, (true, false, true) => x.k
  | .II, (false, true, true) => (1 - x.k) * x.m
  | .II, (false, true, false) => (1 - x.k) * x.l
  | .II, (false, false, false) => (1 - x.k) * (1 - x.l - x.m)
  | _, _ => 0

lemma hypothesisMass_nonneg (x : TwoHypothesesParameters) (hx : x.Feasible) (w) :
    0 ≤ x.hypothesisMass w := by
  cases w with
  | I => exact hx.1
  | II => simp [hypothesisMass]; linarith [hx.2.1]

lemma hypothesisMass_total (x : TwoHypothesesParameters) :
    ∑ w, x.hypothesisMass w = 1 := by
  simp only [TwoHypothesesParameters.hypothesisMass]
  have : (Finset.univ : Finset Hypothesis) = {.I, .II} := by decide
  rw [this]
  simp [Finset.sum]

lemma inferenceMass_nonneg (x : TwoHypothesesParameters) (hx : x.Feasible) (w o) :
    0 ≤ x.inferenceMass w o := by
  rcases hx with ⟨hp_lo, hp_hi, hk_lo, hk_hi, hl_lo, hm_lo, hlm_hi⟩
  cases w <;> fin_cases o <;> simp [inferenceMass]
  all_goals try apply mul_nonneg (sub_nonneg.mpr hk_hi) (by linarith : 0 ≤ 1 - x.l - x.m)
  all_goals try apply mul_nonneg (sub_nonneg.mpr hk_hi); assumption
  all_goals try assumption

lemma inferenceMass_total (x : TwoHypothesesParameters) (w) :
    ∑ o, x.inferenceMass w o = 1 := by
  cases w with
  | I =>
    simp [inferenceMass]
    rw [show (Finset.univ : Finset InferenceOutcome) = {
        (true, true, true), (true, true, false), (true, false, true), (true, false, false),
        (false, true, true), (false, true, false), (false, false, true), (false, false, false)
      } by rfl]
    simp
    ring
  | II =>
    simp [inferenceMass]
    rw [show (Finset.univ : Finset InferenceOutcome) = {
        (true, true, true), (true, true, false), (true, false, true), (true, false, false),
        (false, true, true), (false, true, false), (false, false, true), (false, false, false)
      } by rfl]
    simp
    ring

/-- The finite prior on the two hypotheses. -/
def hypothesisLaw (x : TwoHypothesesParameters) (hx : x.Feasible) : FiniteLaw Hypothesis where
  mass := x.hypothesisMass
  nonneg := x.hypothesisMass_nonneg hx
  total := x.hypothesisMass_total

/-- The inference distribution in either hypothesis. -/
def inferenceLaw (x : TwoHypothesesParameters) (hx : x.Feasible)
    (w : Hypothesis) : FiniteLaw InferenceOutcome where
  mass := x.inferenceMass w
  nonneg := x.inferenceMass_nonneg hx w
  total := x.inferenceMass_total w

/-- Infinite data: the primary firm's training observation identifies the hypothesis,
whereas the secondary firm's observation is uninformative. -/
def trainingLaw (w : Hypothesis) : FiniteLaw (Hypothesis × Unit) where
  mass z := if z.1 = w then 1 else 0
  nonneg z := by split <;> norm_num
  total := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_unique]
    simp

/-- Figure 4 as an instance of the general finite Bayesian environment. -/
def environment (x : TwoHypothesesParameters) (hx : x.Feasible) :
    BayesianEnvironment Hypothesis Hypothesis Unit where
  prior := x.hypothesisLaw hx
  training := trainingLaw
  inference := x.inferenceLaw hx

/-- Population incidence of mutation `A`, as displayed in Section 5.1. -/
def mutationAIncidence (x : TwoHypothesesParameters) : ℝ :=
  x.p * (x.k + (1 - x.k) * x.l) +
    (1 - x.p) * (1 - x.k) * (x.l + x.m)

/-- Population incidence of mutation `B`. -/
def mutationBIncidence (x : TwoHypothesesParameters) : ℝ :=
  1 - x.mutationAIncidence

/-- Matching-recommendations utilities: both correct actions pay one, errors cost zero. -/
def matchingRecommendations : UtilityParameters where
  reward0 := 1
  reward1 := 1
  cost0 := 0
  cost1 := 0
  reward0_nonneg := by norm_num
  reward1_nonneg := by norm_num
  cost0_nonneg := by norm_num
  cost1_nonneg := by norm_num

/-- Equation (15), together with Equation (16). -/
def StructuralConditions (x : TwoHypothesesParameters) : Prop :=
  (1 - x.k) * x.m > 2 * x.k ∧
  (1 - x.k) * (1 - x.l - x.m) / 2 > x.k ∧
  x.k > (1 - x.k) * x.l / 2 ∧
  x.k > (1 - x.k) * x.l

/-- The two inequalities selecting Firm 2's infer-sharing actions on `Aa` and `Ba`. -/
def InferActionConditions (x : TwoHypothesesParameters) : Prop :=
  (1 - x.k) * (1 - x.p) * x.m / 2 > x.k * x.p / 2 ∧
  (1 - x.k) * x.p * x.m / 2 < x.k * (1 - x.p) / 2

/-- No-sharing equilibrium payoffs calculated in Appendix D. -/
noncomputable def noPrimaryPayoff (x : TwoHypothesesParameters) : ℝ :=
  x.k * x.p + (1 - x.k) * (1 - x.p * x.l) / 2

noncomputable def noSecondaryPayoff (x : TwoHypothesesParameters) : ℝ :=
  (1 - x.k) * x.p * x.l / 2 + (1 - x.k) / 2

/-- Infer-sharing equilibrium payoffs calculated in Appendix D. -/
noncomputable def inferPrimaryPayoff (x : TwoHypothesesParameters) : ℝ :=
  1 / 2 + (1 - x.k) * x.p * x.m / 2 + x.k * x.p / 2

noncomputable def inferSecondaryPayoff (x : TwoHypothesesParameters) : ℝ :=
  x.k * (1 - x.p) / 2 + (1 - x.k) * (1 - x.p * x.m) / 2

/-- The primary firm's no-sharing payoff after the training observation identifying I. -/
noncomputable def noPrimaryGivenI (x : TwoHypothesesParameters) : ℝ :=
  x.k + (1 - x.k) * (1 - x.l) / 2

/-- Under full sharing each firm predicts correctly and receives half the market. -/
noncomputable def fullPayoff (_x : TwoHypothesesParameters) : ℝ := 1 / 2

/-- Strict gains of both firms from infer sharing over no sharing. -/
def InferStrictlyImproves (x : TwoHypothesesParameters) : Prop :=
  x.noPrimaryPayoff < x.inferPrimaryPayoff ∧
  x.noSecondaryPayoff < x.inferSecondaryPayoff

/-- The rectangular range printed at the end of Appendix D does **not** imply
Equation (15).  This exact point is a formal counterexample to that claim. -/
noncomputable def printedBoxCounterexample : TwoHypothesesParameters where
  priorI := 1 / 10
  incidence := 3 / 20
  mutationNoise := 1 / 20
  environmentNoise := 21 / 100

lemma printedBoxCounterexample_mem : printedBoxCounterexample.InTheorem51Box := by
  norm_num [printedBoxCounterexample, InTheorem51Box]

lemma printedBoxCounterexample_not_structural :
    ¬ printedBoxCounterexample.StructuralConditions := by
  norm_num [printedBoxCounterexample, StructuralConditions]

lemma theorem51Box_inferActions (x : TwoHypothesesParameters)
    (hx : x.InTheorem51Box) : x.InferActionConditions := by
  unfold InTheorem51Box at hx
  unfold InferActionConditions
  obtain ⟨hp0, hp1, hk0, hk1, hl0, hl1, hm0, hm1⟩ := hx
  have h1mk : 1 - x.k > 5/6 := by linarith
  have h1mp : 1 - x.p > 13/15 := by linarith
  have hkm : x.k * x.p < (1/6) * (2/15) := by nlinarith
  have h1km : (1 - x.k) * (1 - x.p) * x.m > (5/6) * (13/15) * (1/5) := by nlinarith
  have hkm2 : (1 - x.k) * x.p * x.m < (1) * (2/15) * (1/2) := by nlinarith
  have hkp : x.k * (1 - x.p) > (1/12) * (13/15) := by nlinarith
  constructor
  · linarith
  · linarith

lemma theorem51Box_inferStrictlyImproves (x : TwoHypothesesParameters)
    (hx : x.InTheorem51Box) : x.InferStrictlyImproves := by
  obtain ⟨hp_pos, hp_lt, hk_lo, hk_hi, hl_pos, hl_lt, hm_lo, hm_hi⟩ := hx
  unfold InferStrictlyImproves
  constructor
  · unfold noPrimaryPayoff inferPrimaryPayoff
    ring_nf
    nlinarith [mul_pos hp_pos (sub_pos.mpr hk_hi), mul_pos hp_pos (sub_pos.mpr hm_lo)]
  · unfold noSecondaryPayoff inferSecondaryPayoff
    ring_nf
    nlinarith [mul_pos hp_pos (sub_pos.mpr hk_hi)]

lemma fullSharing_fails_primary_IR (x : TwoHypothesesParameters)
    (h16 : x.k > (1 - x.k) * x.l) :
    x.fullPayoff < x.noPrimaryGivenI := by
  simp [fullPayoff, noPrimaryGivenI]
  linarith

/-- Equilibrium payoff vector used in the Appendix-D contract comparison.
No and train sharing coincide under Equation (15). -/
noncomputable def reducedPayoff (x : TwoHypothesesParameters) : Contract → Firm → ℝ
  | .noSharing, .firm1 | .trainSharing, .firm1 => x.noPrimaryPayoff
  | .noSharing, .firm2 | .trainSharing, .firm2 => x.noSecondaryPayoff
  | .inferSharing, .firm1 => x.inferPrimaryPayoff
  | .inferSharing, .firm2 => x.inferSecondaryPayoff
  | .fullSharing, _ => x.fullPayoff

/-- The individual-rationality tests from the proof.  The full-sharing test includes
the hypothesis-I training contingency that blocks full sharing. -/
def ReducedIR (x : TwoHypothesesParameters) : Contract → Prop
  | .noSharing | .trainSharing => True
  | .inferSharing => x.InferStrictlyImproves
  | .fullSharing => x.noPrimaryGivenI ≤ x.fullPayoff

/-- Strict Pareto comparison of the equilibrium payoff vectors. -/
def ReducedStrictlyDominates (x : TwoHypothesesParameters) (c d : Contract) : Prop :=
  (∀ i, x.reducedPayoff d i ≤ x.reducedPayoff c i) ∧
  (∃ i, x.reducedPayoff d i < x.reducedPayoff c i)

/-- IRPO in the reduced equilibrium characterization proved in Appendix D. -/
def IsReducedIRPO (x : TwoHypothesesParameters) (c : Contract) : Prop :=
  x.ReducedIR c ∧ ∀ d, x.ReducedIR d → ¬ x.ReducedStrictlyDominates d c

/-- The strict conditions actually needed by the Appendix-D proof. -/
def InTheorem51Region (x : TwoHypothesesParameters) : Prop :=
  x.InTheorem51Box ∧ x.StructuralConditions ∧
    x.InferActionConditions ∧ x.InferStrictlyImproves

/-- Formal scalar core of Theorem 5.1: under the strict Appendix-D conditions,
infer sharing is the unique IRPO contract in its equilibrium characterization. -/
theorem theorem5_1 (x : TwoHypothesesParameters) (hx : x.InTheorem51Region) :
    x.IsReducedIRPO .inferSharing ∧
      ∀ c, x.IsReducedIRPO c → c = .inferSharing := by
  have hIR : x.InferStrictlyImproves := hx.2.2.2
  have hk_gt : x.k > (1 - x.k) * x.l := hx.2.1.2.2.2
  have hfull : x.fullPayoff < x.noPrimaryGivenI := fullSharing_fails_primary_IR x hk_gt
  have hinfer_dom : x.ReducedStrictlyDominates .inferSharing .noSharing := by
    constructor
    · intro i; cases i <;> simp [reducedPayoff] <;> linarith [hIR.1, hIR.2]
    · exact ⟨.firm1, by simp [reducedPayoff]; exact hIR.1⟩
  have hinfer_dom_ts : x.ReducedStrictlyDominates .inferSharing .trainSharing := by
    constructor
    · intro i; cases i <;> simp [reducedPayoff] <;> linarith [hIR.1, hIR.2]
    · exact ⟨.firm1, by simp [reducedPayoff]; exact hIR.1⟩
  have hNS_not : ¬ x.ReducedStrictlyDominates .noSharing .inferSharing := by
    intro h; rcases h.2 with ⟨i, hi⟩
    cases i <;> simp [reducedPayoff] at hi <;> linarith [hIR.1, hIR.2]
  have hTS_not : ¬ x.ReducedStrictlyDominates .trainSharing .inferSharing := by
    intro h; rcases h.2 with ⟨i, hi⟩
    cases i <;> simp [reducedPayoff] at hi <;> linarith [hIR.1, hIR.2]
  have hFS_not : ¬ x.ReducedIR .fullSharing := by
    simp [ReducedIR]; exact hfull
  have hinfer : x.IsReducedIRPO .inferSharing := by
    constructor
    · simp [ReducedIR, hIR]
    · intro d hd
      cases d with
      | noSharing => exact hNS_not
      | trainSharing => exact hTS_not
      | inferSharing =>
          intro h; rcases h.2 with ⟨i, hi⟩
          cases i <;> simp [reducedPayoff] at hi
      | fullSharing => exact False.elim (hFS_not hd)
  refine ⟨hinfer, ?_⟩
  intro c hc
  cases c with
  | noSharing => exact False.elim (hc.2 .inferSharing (by simp [ReducedIR, hIR]) hinfer_dom)
  | trainSharing => exact False.elim (hc.2 .inferSharing (by simp [ReducedIR, hIR]) hinfer_dom_ts)
  | inferSharing => rfl
  | fullSharing => exact False.elim (hFS_not hc.1)

/-- A concrete rational point certifying that the parameter region is nonempty. -/
noncomputable def theorem51Witness : TwoHypothesesParameters where
  priorI := 1 / 10
  incidence := 1 / 10
  mutationNoise := 1 / 20
  environmentNoise := 3 / 10

lemma theorem51Witness_mem : theorem51Witness.InTheorem51Box := by
  norm_num [theorem51Witness, InTheorem51Box]

lemma theorem51Witness_structural : theorem51Witness.StructuralConditions := by
  norm_num [theorem51Witness, StructuralConditions]

lemma theorem51Witness_region : theorem51Witness.InTheorem51Region := by
  refine ⟨theorem51Witness_mem, theorem51Witness_structural, ?_, ?_⟩
  · exact theorem51Box_inferActions theorem51Witness theorem51Witness_mem
  · exact theorem51Box_inferStrictlyImproves theorem51Witness theorem51Witness_mem

end TwoHypothesesParameters
end TrainSharing
