import RequestProject.Consumer

/-!
# Opportunity-seeking consumers

This file develops Lemma 4.2 and the general quantitative core of Theorem 4.3.
An opportunity-seeking consumer is represented by two outcome values: the value when at
least one firm offers the preferred action and the value when neither does.  This is the
paper's Lemma C.3 normal form after label-independence and consumer choice are imposed.
-/

namespace TrainSharing

/-- Equation (8): the consumer's primitive utility for either action is independent of
its true label. -/
def IsOpportunitySeekingPrimitive (primitive : Bool → Bool → ℝ) : Prop :=
  ∀ action label, primitive action label = primitive action (!label)

/-- A primitive consumer utility, interpreted through the common Section 4 choice rule,
is opportunity-seeking exactly when it is label-independent. -/
theorem opportunitySeeking_consumer_label_independent
    (primitive : Bool → Bool → ℝ) (h : IsOpportunitySeekingPrimitive primitive)
    (a1 a2 label : Bool) :
    consumerChoosesSignificant primitive a1 label a2 =
      consumerChoosesSignificant primitive a1 (!label) a2 := by
  unfold consumerChoosesSignificant
  exact h _ _

/-- Consumer utility in the two-scalar normal form of Lemma C.3. -/
structure OpportunityConsumer where
  preferred : Bool
  successValue : ℝ
  failureValue : ℝ
  strictlyPrefers : failureValue < successValue

/-- Whether at least one firm takes the consumer's preferred action. -/
def preferredAvailable (p : Bool) (a1 a2 : Bool) : Bool := a1 = p || a2 = p

/-- Ex-post opportunity-seeking utility.  It is deliberately independent of the label. -/
def OpportunityConsumer.utility (v : OpportunityConsumer)
    (a1 _label a2 : Bool) : ℝ :=
  if preferredAvailable v.preferred a1 a2 then v.successValue else v.failureValue

/-- Probability that the preferred action is available under an arbitrary finite law. -/
def preferredProbability {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (event : Ω → Bool) : ℝ :=
  ∑ ω, law.mass ω * if event ω then 1 else 0

/-- Expected utility of the two-scalar consumer under an arbitrary finite outcome law. -/
def opportunityExpectedUtility {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (event : Ω → Bool) (v : OpportunityConsumer) : ℝ :=
  ∑ ω, law.mass ω * if event ω then v.successValue else v.failureValue

/-- Lemma 4.2's affine identity: utility is baseline utility plus the utility gap times
probability that at least one firm offers the preferred action. -/
theorem lemma4_2_affine {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (event : Ω → Bool) (v : OpportunityConsumer) :
    opportunityExpectedUtility law event v =
      v.failureValue + (v.successValue - v.failureValue) * preferredProbability law event := by
  simp only [opportunityExpectedUtility, preferredProbability]
  have key : ∀ ω, law.mass ω * (if event ω = true then v.successValue else v.failureValue) =
    law.mass ω * v.failureValue + law.mass ω * (v.successValue - v.failureValue) * (if event ω = true then 1 else 0) := by
    intro ω
    by_cases he : event ω = true
    · simp [he]
      ring
    · simp [he]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  congr 1
  · rw [mul_comm, law.total, mul_one]
  · simp_rw [mul_assoc, mul_comm (v.successValue - v.failureValue)]
    rw [Finset.sum_mul]
    simp_rw [mul_assoc]

/-- Lemma 4.2: comparing expected utilities is exactly comparing probabilities of trade. -/
theorem lemma4_2_maximization_equiv {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (first second : Ω → Bool) (v : OpportunityConsumer) :
    opportunityExpectedUtility law first v ≤ opportunityExpectedUtility law second v ↔
      preferredProbability law first ≤ preferredProbability law second := by
  rw [lemma4_2_affine, lemma4_2_affine]
  simp only [add_le_add_iff_left]
  have hpos : 0 < v.successValue - v.failureValue := sub_pos.mpr v.strictlyPrefers
  exact mul_le_mul_iff_of_pos_left hpos

/-- The normalized consumer used in the quantitative statements has expected utility
exactly equal to the probability of trade. -/
theorem lemma4_2_normalized {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (event : Ω → Bool) (p : Bool) :
    opportunityExpectedUtility law event
      { preferred := p, successValue := 1, failureValue := 0, strictlyPrefers := by norm_num } =
      preferredProbability law event := by
  rw [lemma4_2_affine]
  simp

/-- Pointwise permissiveness implies the consumer comparison in Theorem 4.3(1).  This is
what the paper's known-correlation and symmetric-reward calculations establish for the
no-sharing equilibrium relative to each rival equilibrium. -/
theorem theorem4_3_part1_of_pointwise_permissive {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (noSharingEvent rivalEvent : Ω → Bool)
    (hperm : ∀ ω, rivalEvent ω = true → noSharingEvent ω = true) :
    preferredProbability law rivalEvent ≤ preferredProbability law noSharingEvent := by
  unfold preferredProbability
  apply Finset.sum_le_sum
  intro ω _
  by_cases hr : rivalEvent ω = true
  · have hn := hperm ω hr
    simp [hr, hn]
  · simp [hr]
    split <;> simp [law.nonneg ω]

/-- A probability of an event is always at most one. -/
theorem preferredProbability_le_one {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (event : Ω → Bool) :
    preferredProbability law event ≤ 1 := by
  unfold preferredProbability
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rw [← law.total]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro ω _ _
    exact law.nonneg ω

/-- The factor-two upper bound in Theorem 4.3(2).  The model-specific premise is exactly
the paper's claim that a nontrivial monotone no-sharing equilibrium trades with probability
at least `1/2`; every rival contract's trade probability is at most one. -/
theorem theorem4_3_part2_factor_two {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (noSharingEvent rivalEvent : Ω → Bool)
    (hhalf : 1 / 2 ≤ preferredProbability law noSharingEvent) :
    preferredProbability law rivalEvent ≤ 2 * preferredProbability law noSharingEvent := by
  have hrival : preferredProbability law rivalEvent ≤ 1 := preferredProbability_le_one law rivalEvent
  have h1 : (1 : ℝ) ≤ 2 * preferredProbability law noSharingEvent := by linarith
  linarith

/-- The event-theoretic core of Theorem 4.6(1): if a no-sharing equilibrium is
pointwise at least as conducive to trade as a train-sharing equilibrium, then the
opportunity-seeking consumer weakly prefers that no-sharing equilibrium.  The economic
part of the theorem is precisely the existence of such an equilibrium. -/
theorem theorem4_6_part1_of_pointwise_permissive {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (trainSharingEvent noSharingEvent : Ω → Bool)
    (hperm : ∀ ω, trainSharingEvent ω = true → noSharingEvent ω = true) :
    preferredProbability law trainSharingEvent ≤
      preferredProbability law noSharingEvent :=
  theorem4_3_part1_of_pointwise_permissive law noSharingEvent trainSharingEvent hperm

/-- The factor-two conclusion of Theorem 4.6(2).  It applies to the best
train-sharing equilibrium for the consumer once the model-specific equilibrium argument
establishes that this equilibrium trades with probability at least one half. -/
theorem theorem4_6_part2_factor_two {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (bestTrainSharingEvent rivalEvent : Ω → Bool)
    (hhalf : 1 / 2 ≤ preferredProbability law bestTrainSharingEvent) :
    preferredProbability law rivalEvent ≤
      2 * preferredProbability law bestTrainSharingEvent :=
  theorem4_3_part2_factor_two law bestTrainSharingEvent rivalEvent hhalf

/-- Theorem 4.6 packaged at the probability-of-trade level.  Its two model-specific
outputs are made explicit: a no-sharing equilibrium whose event contains the selected
train-sharing event, and the half-probability guarantee for the consumer-best
train-sharing equilibrium.  The conclusion simultaneously records part (1) and the
part (2) bound against every rival contract/equilibrium event. -/
theorem theorem4_6_of_equilibrium_characterization {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (bestTrainSharingEvent noSharingEvent : Ω → Bool)
    (rivalEvents : Contract → Ω → Bool)
    (hperm : ∀ ω, bestTrainSharingEvent ω = true → noSharingEvent ω = true)
    (hhalf : 1 / 2 ≤ preferredProbability law bestTrainSharingEvent) :
    preferredProbability law bestTrainSharingEvent ≤
        preferredProbability law noSharingEvent ∧
      ∀ c, preferredProbability law (rivalEvents c) ≤
        2 * preferredProbability law bestTrainSharingEvent := by
  constructor
  · exact theorem4_6_part1_of_pointwise_permissive law bestTrainSharingEvent
      noSharingEvent hperm
  · intro c
    exact theorem4_6_part2_factor_two law bestTrainSharingEvent (rivalEvents c) hhalf

/-- Strict version of Theorem 4.6(1), useful for the paper's numerical witness.  A
strictly larger probability gives the claimed strict consumer preference by Lemma 4.2. -/
theorem theorem4_6_part1_strict {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (trainSharingEvent noSharingEvent : Ω → Bool)
    (htrade : preferredProbability law trainSharingEvent <
      preferredProbability law noSharingEvent) (v : OpportunityConsumer) :
    opportunityExpectedUtility law trainSharingEvent v <
      opportunityExpectedUtility law noSharingEvent v := by
  rw [lemma4_2_affine, lemma4_2_affine]
  have hgap : 0 < v.successValue - v.failureValue := sub_pos.mpr v.strictlyPrefers
  nlinarith

end TrainSharing
