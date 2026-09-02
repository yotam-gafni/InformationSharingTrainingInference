import RequestProject.BayesianGame
import RequestProject.KnownCorrelation

/-!
# Unknown-correlation value-of-information results

This file formalizes the numerical core of Lemma 3.5.  For each inference-signal pair,
`score w q` is the (prior-weighted) gain from taking the significant action in world `w`.
Infer-sharing must choose before learning `w`, and therefore receives the positive part of
the aggregate score.  Full-sharing observes `w`, and receives the aggregate of the
world-by-world positive parts.  The latter is weakly larger.

We also introduce contract equivalence and uniqueness up to equivalence, so conclusions
remain meaningful when no-sharing/train-sharing or infer-sharing/full-sharing induce the
same information and payoffs.
-/

namespace TrainSharing

variable {World Train1 Train2 : Type}
  [Fintype World] [Fintype Train1] [Fintype Train2]

/-- Two contracts are equivalent when they Pareto-dominate one another. -/
def ContractEquivalent
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (c d : Contract) : Prop :=
  ParetoDominates E u c d ∧ ParetoDominates E u d c

/-- Unique IRPO modulo payoff-equivalent contracts. -/
def IsUniquelyIRPOUpToEquivalence
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (c : Contract) : Prop :=
  IsIRPO E u c ∧ ∀ d, IsIRPO E u d → ContractEquivalent E u d c

/-- Literal uniqueness implies uniqueness up to equivalence (dominance is reflexive at
`c` under the explicitly stated reflexivity assumption). -/
theorem uniquelyIRPO_implies_uniqueUpToEquivalence
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) (c : Contract)
    (hrefl : ParetoDominates E u c c)
    (h : IsUniquelyIRPO E u c) :
    IsUniquelyIRPOUpToEquivalence E u c := by
  constructor
  · exact h.1
  · intro d hd
    have hdc : d = c := h.2 d hd
    subst d
    exact ⟨hrefl, hrefl⟩

/-- A general IRPO reduction used by Theorem 3.6: if `c` dominates every contract,
then it is IRPO and every other IRPO contract is equivalent to it.  This formulation
correctly allows several syntactically different but payoff-equivalent contracts. -/
theorem universallyDominating_is_uniqueIRPOUpToEquivalence
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) (c : Contract)
    (hall : ∀ d, ParetoDominates E u c d) :
    IsUniquelyIRPOUpToEquivalence E u c := by
  constructor
  · -- IsIRPO E u c
    constructor
    · -- IsIndividuallyRational E u c
      right
      exact hall .noSharing
    · -- IsParetoOptimal E u c
      intro d hd
      exact hd.2 (hall d)
  · -- ∀ d, IsIRPO E u d → ContractEquivalent E u d c
    intro d hdIRPO
    constructor
    · -- Need to show ParetoDominates E u d c
      by_contra hnot
      -- If c dominates d but d doesn't dominate c, then c strictly dominates d
      have hstrict : StrictlyParetoDominates E u c d := ⟨hall d, hnot⟩
      -- But d is IRPO, hence Pareto optimal
      exact hdIRPO.2 c hstrict
    · exact hall d

/-- If the universally dominating contract has no equivalent rival, literal unique IRPO
follows.  This is the appropriate strengthened conclusion away from equivalence cases. -/
theorem universallyDominating_is_uniquelyIRPO
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) (c : Contract)
    (hall : ∀ d, ParetoDominates E u c d)
    (hsep : ∀ d, ParetoDominates E u d c → ParetoDominates E u c d → d = c) :
    IsUniquelyIRPO E u c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  -- IsIndividuallyRational E u c
  · right
    exact hall .noSharing
  -- IsParetoOptimal E u c
  · intro d hd
    rw [StrictlyParetoDominates] at hd
    exact hd.2 (hall d)
  -- ∀ d, IsIRPO E u d → d = c
  · intro d hd
    rcases hd.1 with rfl | hdom_nosharing
    · -- d = .noSharing, need to show .noSharing = c
      -- We have ParetoDominates E u c .noSharing, and .noSharing is Pareto optimal
      have hno : ¬ StrictlyParetoDominates E u c .noSharing := hd.2 c
      rw [StrictlyParetoDominates] at hno
      push_neg at hno
      exact hsep .noSharing (hno (hall .noSharing)) (hall .noSharing)
    · -- d Pareto dominates .noSharing, and d is Pareto optimal
      -- We have ParetoDominates E u c d from hall
      -- Need to show ParetoDominates E u d c
      -- If not, then StrictlyParetoDominates E u c d, contradicting d being Pareto optimal
      have hcdd : ParetoDominates E u c d := hall d
      have hd_ipo : IsParetoOptimal E u d := hd.2
      have hdom_dc : ParetoDominates E u d c := by
        by_contra hneg
        have : StrictlyParetoDominates E u c d := ⟨hcdd, hneg⟩
        exact hd_ipo c this
      exact hsep d hdom_dc hcdd

namespace Correlation.Unknown

variable {W Q : Type} [Fintype W] [Fintype Q]

/-- Full-sharing value: the world is known before the significant-action decision. -/
noncomputable def fullSharingValue (score : W → Q → ℝ) : ℝ :=
  ∑ q, ∑ w, max 0 (score w q)

/-- Infer-sharing value: only the inference signal pair is known; the world is averaged
before the significant-action decision. -/
noncomputable def inferSharingValue (score : W → Q → ℝ) : ℝ :=
  ∑ q, max 0 (∑ w, score w q)

/-- Positive-part subadditivity for a finite family. -/
theorem max_zero_sum_le_sum_max_zero (f : W → ℝ) :
    max 0 (∑ w, f w) ≤ ∑ w, max 0 (f w) := by
  rcases le_or_gt (∑ w, f w) 0 with h | h
  · simp [max_eq_left h]
    exact Finset.sum_nonneg fun _ _ => le_max_left _ _
  · simp [max_eq_right (le_of_lt h)]
    exact Finset.sum_le_sum fun _ _ => le_max_right _ _

/-- Lemma 3.5's value-of-information inequality: revealing the correlation before the
action cannot lower either firm's equilibrium value when both firms have the same shared
inference information and use the symmetric significant-action equilibrium. -/
theorem fullSharing_ge_inferSharing (score : W → Q → ℝ) :
    inferSharingValue score ≤ fullSharingValue score := by
  unfold inferSharingValue fullSharingValue
  exact Finset.sum_le_sum fun q _ => max_zero_sum_le_sum_max_zero (fun w => score w q)

/-- The same statement with the market-splitting factor `1/2` appearing in the paper. -/
theorem fullSharing_ge_inferSharing_half (score : W → Q → ℝ) :
    (1 / 2 : ℝ) * inferSharingValue score ≤
      (1 / 2 : ℝ) * fullSharingValue score := by
  exact mul_le_mul_of_nonneg_left (fullSharing_ge_inferSharing score) (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-! ## Link to the paper's correlation model

The abstract `score` above is now instantiated with the balanced-label conditional masses
of the correlation model.  This closes the modeling link: the two values below are not
free numerical placeholders, but exactly the significant-action expected gains generated
by a prior over correlations.
-/

open TrainSharing.Correlation.Known

/-- Prior-weighted significant-action score in a correlation world. -/
noncomputable def correlationScore (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta reward cost : ℝ) (w : W) (q : Bool × Bool) : ℝ :=
  prior.mass w * (reward * conditionalMass alpha beta (rho w) true q.1 q.2 -
    cost * conditionalMass alpha beta (rho w) false q.1 q.2)

/-- Infer-sharing equilibrium payoff for either firm in the correlation model. -/
noncomputable def correlationInferPayoff (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta reward cost : ℝ) : ℝ :=
  (1 / 2 : ℝ) * inferSharingValue
    (correlationScore prior rho alpha beta reward cost)

/-- Full-sharing equilibrium payoff for either firm in the correlation model. -/
noncomputable def correlationFullPayoff (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta reward cost : ℝ) : ℝ :=
  (1 / 2 : ℝ) * fullSharingValue
    (correlationScore prior rho alpha beta reward cost)

/-- Fully linked Lemma 3.5: for every finite prior over realized correlations and every
reward and cost, each firm's full-sharing payoff weakly exceeds its infer-sharing payoff.
The two firms have the same payoff because both contracts produce the symmetric shared-
inference equilibrium. -/
theorem lemma3_5_correlation_full_ge_infer (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta reward cost : ℝ) :
    correlationInferPayoff prior rho alpha beta reward cost ≤
      correlationFullPayoff prior rho alpha beta reward cost := by
  exact fullSharing_ge_inferSharing_half
    (correlationScore prior rho alpha beta reward cost)

/-- The preceding scalar comparison simultaneously gives the paper's two Pareto
inequalities, one for each (symmetric) firm. -/
theorem lemma3_5_correlation_pareto_pair (prior : FiniteLaw W) (rho : W → ℝ)
    (alpha beta reward cost : ℝ) :
    correlationInferPayoff prior rho alpha beta reward cost ≤
        correlationFullPayoff prior rho alpha beta reward cost ∧
      correlationInferPayoff prior rho alpha beta reward cost ≤
        correlationFullPayoff prior rho alpha beta reward cost := by
  exact ⟨lemma3_5_correlation_full_ge_infer prior rho alpha beta reward cost,
    lemma3_5_correlation_full_ge_infer prior rho alpha beta reward cost⟩

end Correlation.Unknown
end TrainSharing
