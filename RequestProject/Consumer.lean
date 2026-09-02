import RequestProject.Theorem36

/-!
# Consumers and aligned consumers

This file formalizes the consumer framework of Section 4, Appendix C.1, and both parts of
Theorem 4.1.  Consumer utility is evaluated on the two firms' actions and the true label.
The order of arguments follows the manuscript: Firm 1's action, label, Firm 2's action.
-/

namespace TrainSharing

/-- A consumer's ex-post utility from the two offered actions and the true label. -/
abbrev ConsumerUtility := Bool → Bool → Bool → ℝ

/-- The consumer chooses the significant action whenever it is offered.  Thus a primitive
single-action utility induces the manuscript's three-argument utility by taking the `or`
of the two firms' actions. -/
def consumerChoosesSignificant (primitive : Bool → Bool → ℝ) : ConsumerUtility :=
  fun a1 label a2 => primitive (a1 || a2) label

/-- Expected consumer utility under an arbitrary finite law of action/label outcomes. -/
def consumerExpectedUtility {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (outcome : Ω → Bool × Bool × Bool) (v : ConsumerUtility) : ℝ :=
  ∑ ω, law.mass ω * v (outcome ω).1 (outcome ω).2.1 (outcome ω).2.2

/-- Equation (7): consumer and firm welfare agree at every ex-post outcome. -/
def IsAlignedConsumer (v : ConsumerUtility) (u : UtilityFamily) : Prop :=
  ∀ a1 label a2,
    v a1 label a2 = u .firm1 a1 label a2 + u .firm2 a2 label a1

/-- The aligned consumer canonically induced by a family of firm utilities. -/
def alignedConsumer (u : UtilityFamily) : ConsumerUtility :=
  fun a1 label a2 => u .firm1 a1 label a2 + u .firm2 a2 label a1

@[simp] theorem alignedConsumer_isAligned (u : UtilityFamily) :
    IsAlignedConsumer (alignedConsumer u) u := by
  intro a1 label a2
  rfl

/-- Expected utility of one firm under an arbitrary finite outcome law. -/
def firmExpectedUtility {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (outcome : Ω → Bool × Bool × Bool) (u : UtilityFamily) (i : Firm) : ℝ :=
  ∑ ω, law.mass ω *
    match i with
    | .firm1 => u .firm1 (outcome ω).1 (outcome ω).2.1 (outcome ω).2.2
    | .firm2 => u .firm2 (outcome ω).2.2 (outcome ω).2.1 (outcome ω).1

/-- Lemma C.2: under any finite outcome law, an aligned consumer's expected utility is
exactly the sum of the two firms' expected utilities. -/
theorem lemmaC_2_aligned_expected_eq_firm_sum {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (outcome : Ω → Bool × Bool × Bool)
    (v : ConsumerUtility) (u : UtilityFamily) (halign : IsAlignedConsumer v u) :
    consumerExpectedUtility law outcome v =
      firmExpectedUtility law outcome u .firm1 +
        firmExpectedUtility law outcome u .firm2 := by
  unfold consumerExpectedUtility firmExpectedUtility
  simp only []
  rw [← Finset.sum_add_distrib]
  congr 1
  funext ω
  rw [halign]
  ring

/-- A direct consequence of Lemma C.2: weak improvements for both firms imply a weak
improvement for every aligned consumer. -/
theorem alignedConsumer_prefers_of_firm_improvements {Ω Ω' : Type*}
    [Fintype Ω] [Fintype Ω'] (law : FiniteLaw Ω) (law' : FiniteLaw Ω')
    (outcome : Ω → Bool × Bool × Bool) (outcome' : Ω' → Bool × Bool × Bool)
    (v : ConsumerUtility) (u : UtilityFamily) (halign : IsAlignedConsumer v u)
    (h1 : firmExpectedUtility law outcome u .firm1 ≤
      firmExpectedUtility law' outcome' u .firm1)
    (h2 : firmExpectedUtility law outcome u .firm2 ≤
      firmExpectedUtility law' outcome' u .firm2) :
    consumerExpectedUtility law outcome v ≤ consumerExpectedUtility law' outcome' v := by
  rw [lemmaC_2_aligned_expected_eq_firm_sum law outcome v u halign, lemmaC_2_aligned_expected_eq_firm_sum law' outcome' v u halign]
  exact add_le_add h1 h2

/-- Significant-action utility of a consumer in Lemma C.1: zero if no firm acts, reward
`R₁` on a positive label if at least one acts, and cost `-C₁` on a negative label. -/
def significantAlignedConsumer (reward1 cost1 : ℝ) : ConsumerUtility :=
  consumerChoosesSignificant fun action label =>
    if action then (if label then reward1 else -cost1) else 0

/-- Lemma C.1: the canonical aligned consumer induced by significant-action firm utility
has exactly the loan interpretation stated in the manuscript. -/
theorem lemmaC_1_significant_aligned_behavior (p : UtilityParameters)
    (hsig : p.IsSignificantAction) (a1 label a2 : Bool) :
    alignedConsumer p.family a1 label a2 =
      significantAlignedConsumer p.reward1 p.cost1 a1 label a2 := by
  obtain ⟨hr0, hc0⟩ := hsig
  cases a1 <;> cases a2 <;> cases label <;> simp [alignedConsumer, significantAlignedConsumer, consumerChoosesSignificant, UtilityParameters.family, UtilityParameters.exPost, hr0, hc0]

/-- Contract-order premise used by Theorem 4.1(1): a uniquely IRPO contract distinct
from no sharing Pareto dominates no sharing by individual rationality. -/
theorem theorem4_1_part1_unique_irpo_dominates_no
    {World Train1 Train2 : Type} [Fintype World] [Fintype Train1] [Fintype Train2]
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily) (c : Contract)
    (hunique : IsUniquelyIRPO E u c) (hc : c ≠ .noSharing) :
    ParetoDominates E u c .noSharing := by
  rcases hunique.1.1 with hno | hdom
  · exact False.elim (hc hno)
  · exact hdom

/-- Theorem 4.1(1), at the general expected-utility layer: the individual-rationality
comparison with no sharing benefits every aligned consumer.  Together with
`theorem4_1_part1_unique_irpo_dominates_no`, this is the manuscript's first clause. -/
theorem theorem4_1_part1_aligned_prefers_ir_improvement {Ωno Ωc : Type*}
    [Fintype Ωno] [Fintype Ωc]
    (noLaw : FiniteLaw Ωno) (contractLaw : FiniteLaw Ωc)
    (noOutcome : Ωno → Bool × Bool × Bool)
    (contractOutcome : Ωc → Bool × Bool × Bool)
    (v : ConsumerUtility) (u : UtilityFamily) (halign : IsAlignedConsumer v u)
    (hfirm1 : firmExpectedUtility noLaw noOutcome u .firm1 ≤
      firmExpectedUtility contractLaw contractOutcome u .firm1)
    (hfirm2 : firmExpectedUtility noLaw noOutcome u .firm2 ≤
      firmExpectedUtility contractLaw contractOutcome u .firm2) :
    consumerExpectedUtility noLaw noOutcome v ≤
      consumerExpectedUtility contractLaw contractOutcome v := by
  exact alignedConsumer_prefers_of_firm_improvements noLaw contractLaw noOutcome
    contractOutcome v u halign hfirm1 hfirm2

/-- The consumer welfare generated on an information atom by significant-action utility.
`netValue ω` is the conditional expected reward (reward times success probability minus
cost times failure probability), and `acts ω` records whether either firm acts. -/
def significantConsumerWelfare {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (netValue : Ω → ℝ) (acts : Ω → Bool) : ℝ :=
  ∑ ω, law.mass ω * if acts ω then netValue ω else 0

/-- Full sharing's action rule: act exactly on information atoms with positive conditional
net value (ties are resolved toward the benign action). -/
noncomputable def fullInformationAction {Ω : Type*} (netValue : Ω → ℝ) (ω : Ω) : Bool :=
  decide (0 < netValue ω)

/-- The key information-refinement inequality in the proof of Theorem 4.1(2): choosing
separately on every full-information atom obtains the positive part of its net value and
weakly dominates every other induced action event. -/
theorem fullInformationAction_maximizes_welfare {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (netValue : Ω → ℝ) (acts : Ω → Bool) :
    significantConsumerWelfare law netValue acts ≤
      significantConsumerWelfare law netValue (fullInformationAction netValue) := by
  unfold significantConsumerWelfare
  apply Finset.sum_le_sum
  intro ω _
  by_cases hpos : 0 < netValue ω
  · simp [fullInformationAction, hpos]
    by_cases hActs : acts ω
    · simp [hActs]
    · simp [hActs]
      exact mul_nonneg (law.nonneg ω) hpos.le
  · have hle : netValue ω ≤ 0 := le_of_not_gt hpos
    simp [fullInformationAction, hpos]
    by_cases hActs : acts ω
    · simp [hActs]
      exact mul_nonpos_of_nonneg_of_nonpos (law.nonneg ω) hle
    · simp [hActs]

/-- Theorem 4.1(2): with significant-action utilities, the aligned consumer weakly
prefers full sharing to every other contract's induced behavior.  The full-sharing
information atoms may include all training information, both inference signals, and the
revealed world; `acts` is the event induced on those same atoms by any rival contract. -/
theorem theorem4_1_part2_aligned_prefers_full_sharing {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (netValue : Ω → ℝ) (rivalAction : Contract → Ω → Bool) :
    ∀ c, significantConsumerWelfare law netValue (rivalAction c) ≤
      significantConsumerWelfare law netValue (fullInformationAction netValue) := by
  intro c
  exact fullInformationAction_maximizes_welfare law netValue (rivalAction c)

end TrainSharing
