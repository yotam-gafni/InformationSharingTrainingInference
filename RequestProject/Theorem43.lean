import RequestProject.NumericalResults
import RequestProject.ModelConnections

/-!
# Theorem 4.3: generic factor-two argument

This file removes the event-level assumptions from the generic upper bound.  It derives
the half-probability lower bound from the correlation model's balanced signal marginals
and the monotonicity of a nontrivial no-sharing equilibrium.
-/

namespace TrainSharing.Theorem43

open TrainSharing.Correlation.Known
open TrainSharing.Correlation.Known.Asymmetric

/-- At least one firm takes the significant action at an inference-signal pair. -/
def tradeEvent (s1 s2 : Bool → Bool) (q : Bool × Bool) : Bool := s1 q.1 || s2 q.2

/-- The profile is nontrivial when at least one firm acts at some signal. -/
def NontrivialProfile (s1 s2 : Bool → Bool) : Prop :=
  (∃ x, s1 x = true) ∨ ∃ y, s2 y = true

/-- The unconditional law of the two inference signals in one balanced-label correlation
world. -/
noncomputable def balancedInferenceLaw (alpha beta rho : ℝ)
    (hnonneg : ∀ label x y, 0 ≤ conditionalMass alpha beta rho label x y)
    (htotal : ∑ q : Bool × Bool,
      ((conditionalMass alpha beta rho true q.1 q.2 +
        conditionalMass alpha beta rho false q.1 q.2) / 2) = 1) :
    FiniteLaw (Bool × Bool) where
  mass q := (conditionalMass alpha beta rho true q.1 q.2 +
    conditionalMass alpha beta rho false q.1 q.2) / 2
  nonneg q := div_nonneg (add_nonneg (hnonneg true q.1 q.2) (hnonneg false q.1 q.2)) (by norm_num)
  total := htotal

/-- In every balanced-label correlation world, each binary signal is unconditionally
balanced. -/
lemma balancedInferenceLaw_marginals (alpha beta rho : ℝ)
    (hnonneg : ∀ label x y, 0 ≤ conditionalMass alpha beta rho label x y)
    (htotal : ∑ q : Bool × Bool,
      ((conditionalMass alpha beta rho true q.1 q.2 +
        conditionalMass alpha beta rho false q.1 q.2) / 2) = 1) :
    (∑ y, (balancedInferenceLaw alpha beta rho hnonneg htotal).mass (true, y)) = 1 / 2 ∧
    (∑ x, (balancedInferenceLaw alpha beta rho hnonneg htotal).mass (x, true)) = 1 / 2 := by
  constructor <;> simp [balancedInferenceLaw, conditionalMass] <;> ring

/-- Purely probabilistic core: under balanced marginals, every nontrivial profile trades
with probability at least one half.  The monotonicity assertion used in the paper's proof
is unnecessary: whichever signal triggers the first action has unconditional probability
one half. -/
theorem half_le_trade_of_nontrivial
    (law : FiniteLaw (Bool × Bool))
    (hfirst : ∑ y, law.mass (true, y) = 1 / 2)
    (hfirstFalse : ∑ y, law.mass (false, y) = 1 / 2)
    (hsecond : ∑ x, law.mass (x, true) = 1 / 2)
    (hsecondFalse : ∑ x, law.mass (x, false) = 1 / 2)
    (s1 s2 : Bool → Bool) (hnontrivial : NontrivialProfile s1 s2) :
    1 / 2 ≤ preferredProbability law (tradeEvent s1 s2) := by
  rcases hnontrivial with ⟨x, hx⟩ | ⟨y, hy⟩
  · have hp := theorem4_3_part1_of_pointwise_permissive law
        (tradeEvent s1 s2) (fun q : Bool × Bool => q.1 = x)
        (by
          intro q hq
          have hqx : q.1 = x := of_decide_eq_true hq
          simp [tradeEvent, hqx, hx])
    have he : preferredProbability law (fun q : Bool × Bool => q.1 = x) = 1 / 2 := by
      cases x
      · rw [← hfirstFalse]
        unfold preferredProbability
        rw [show (Finset.univ : Finset (Bool × Bool)) =
          {(true, true), (true, false), (false, true), (false, false)} by decide]
        simp
      · rw [← hfirst]
        unfold preferredProbability
        rw [show (Finset.univ : Finset (Bool × Bool)) =
          {(true, true), (true, false), (false, true), (false, false)} by decide]
        simp
    linarith
  · have hp := theorem4_3_part1_of_pointwise_permissive law
        (tradeEvent s1 s2) (fun q : Bool × Bool => q.2 = y)
        (by
          intro q hq
          have hqy : q.2 = y := of_decide_eq_true hq
          simp [tradeEvent, hqy, hy])
    have he : preferredProbability law (fun q : Bool × Bool => q.2 = y) = 1 / 2 := by
      cases y
      · rw [← hsecondFalse]
        unfold preferredProbability
        rw [show (Finset.univ : Finset (Bool × Bool)) =
          {(true, true), (true, false), (false, true), (false, false)} by decide]
        simp
      · rw [← hsecond]
        unfold preferredProbability
        rw [show (Finset.univ : Finset (Bool × Bool)) =
          {(true, true), (true, false), (false, true), (false, false)} by decide]
        simp
    linarith

/-- The nontriviality premise is necessary at the strategy level.  If both firms are
inactive, no sharing has zero trade probability, while an always-trading rival has
probability one, so no finite factor (in particular two) can compare them. -/
theorem inactive_profile_counterexample :
    let law : FiniteLaw (Bool × Bool) :=
      { mass := fun _ => 1 / 4
        nonneg := by intro; norm_num
        total := by norm_num [Finset.sum_eq_add_sum_diff_singleton] }
    let inactive : Bool → Bool := fun _ => false
    preferredProbability law (fun _ => true) >
      2 * preferredProbability law (tradeEvent inactive inactive) := by
  norm_num [preferredProbability, tradeEvent, Finset.sum_eq_add_sum_diff_singleton]

/-- Generic factor-two bound for any mixture over correlations.  It uses only the four
balanced unconditional signal marginals and nontriviality of the selected no-sharing
profile; it does not assume a pre-packaged half-probability condition. -/
theorem factor_two_of_nontrivial
    (law : FiniteLaw (Bool × Bool))
    (hfirst : ∑ y, law.mass (true, y) = 1 / 2)
    (hfirstFalse : ∑ y, law.mass (false, y) = 1 / 2)
    (hsecond : ∑ x, law.mass (x, true) = 1 / 2)
    (hsecondFalse : ∑ x, law.mass (x, false) = 1 / 2)
    (s1 s2 : Bool → Bool) (hnontrivial : NontrivialProfile s1 s2)
    (rivalEvent : Bool × Bool → Bool) :
    preferredProbability law rivalEvent ≤
      2 * preferredProbability law (tradeEvent s1 s2) := by
  apply theorem4_3_part2_factor_two
  exact half_le_trade_of_nontrivial law hfirst hfirstFalse hsecond hsecondFalse
    s1 s2 hnontrivial

/-- In the concrete correlation model, the generic factor-two bound has no event-level
conditional premise: balanced marginals are calculated from the model itself.  The more
general preceding theorem applies directly to an arbitrary distribution over correlations,
since mixtures preserve these four marginal equalities. -/
theorem correlation_factor_two
    (alpha beta rho : ℝ)
    (hnonneg : ∀ label x y, 0 ≤ conditionalMass alpha beta rho label x y)
    (htotal : ∑ q : Bool × Bool,
      ((conditionalMass alpha beta rho true q.1 q.2 +
        conditionalMass alpha beta rho false q.1 q.2) / 2) = 1)
    (s1 s2 : Bool → Bool) (hnontrivial : NontrivialProfile s1 s2)
    (rivalEvent : Bool × Bool → Bool) :
    preferredProbability (balancedInferenceLaw alpha beta rho hnonneg htotal) rivalEvent ≤
      2 * preferredProbability (balancedInferenceLaw alpha beta rho hnonneg htotal)
        (tradeEvent s1 s2) := by
  apply factor_two_of_nontrivial
  · exact (balancedInferenceLaw_marginals alpha beta rho hnonneg htotal).1
  · simp [balancedInferenceLaw, conditionalMass]
    ring
  · exact (balancedInferenceLaw_marginals alpha beta rho hnonneg htotal).2
  · simp [balancedInferenceLaw, conditionalMass]
    ring
  · exact hnontrivial

/-- The unconditional inference-signal law obtained directly from a feasible correlation
parameter tuple.  Unlike `balancedInferenceLaw`, its probability-law obligations are
proved by the primitive `Parameters.world` construction rather than supplied as premises. -/
noncomputable def parameterInferenceLaw
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) :
    FiniteLaw (Bool × Bool) where
  mass q := ((p.world hp).signals true).mass q / 2 +
    ((p.world hp).signals false).mass q / 2
  nonneg q := add_nonneg (div_nonneg (((p.world hp).signals true).nonneg q) (by norm_num))
    (div_nonneg (((p.world hp).signals false).nonneg q) (by norm_num))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ((p.world hp).signals true).total, ((p.world hp).signals false).total]
    norm_num

/-- Both signal marginals are fair under the primitive correlation model. -/
theorem parameterInferenceLaw_marginals
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) :
    (∑ y, (parameterInferenceLaw p hp).mass (true, y)) = 1 / 2 ∧
    (∑ y, (parameterInferenceLaw p hp).mass (false, y)) = 1 / 2 ∧
    (∑ x, (parameterInferenceLaw p hp).mass (x, true)) = 1 / 2 ∧
    (∑ x, (parameterInferenceLaw p hp).mass (x, false)) = 1 / 2 := by
  simp [parameterInferenceLaw, TrainSharing.Correlation.Parameters.world,
    TrainSharing.Correlation.Parameters.signalLaw,
    TrainSharing.Correlation.Parameters.jointMass,
    TrainSharing.Correlation.Parameters.jointTT]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Theorem 4.3's factor-two calculation directly from a feasible correlation-model
world.  The only strategic premise left is nontriviality of the selected no-sharing
profile; `inactive_profile_counterexample` proves that this premise cannot be erased from
the mathematical statement. -/
theorem theorem4_3_factor_two_from_correlation_model
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible)
    (s1 s2 : Bool → Bool) (hnontrivial : NontrivialProfile s1 s2)
    (rivalEvent : Bool × Bool → Bool) :
    preferredProbability (parameterInferenceLaw p hp) rivalEvent ≤
      2 * preferredProbability (parameterInferenceLaw p hp) (tradeEvent s1 s2) := by
  rcases parameterInferenceLaw_marginals p hp with ⟨h1, h0, h2, h3⟩
  exact factor_two_of_nontrivial (parameterInferenceLaw p hp) h1 h0 h2 h3
    s1 s2 hnontrivial rivalEvent

/-- Literal unique IRPO is a property of a Bayesian environment and cannot, by itself,
replace `NontrivialProfile` in the lower-level correlation probability theorem when the
profile and correlation parameters are not connected to that environment.  Indeed, even
assuming no sharing is literally uniquely IRPO, the universally inactive profile has
zero trade while the always-true rival event has probability one.  This is the precise
counterexample to the proposed premise substitution in the current formal interface. -/
theorem uniqueIRPO_alone_cannot_replace_nontrivial
    {World Train1 Train2 : Type}
    [Fintype World] [Fintype Train1] [Fintype Train2]
    (E : BayesianEnvironment World Train1 Train2) (u : UtilityFamily)
    (_hunique : IsUniquelyIRPO E u .noSharing)
    (p : TrainSharing.Correlation.Parameters) (hp : p.Feasible) :
    ¬ (∀ (s1 s2 : Bool → Bool) (rivalEvent : Bool × Bool → Bool),
      preferredProbability (parameterInferenceLaw p hp) rivalEvent ≤
        2 * preferredProbability (parameterInferenceLaw p hp) (tradeEvent s1 s2)) := by
  push_neg
  use fun _ => false, fun _ => false, fun _ => true
  simp [tradeEvent, preferredProbability]
  have h := (parameterInferenceLaw p hp).total
  linarith

end TrainSharing.Theorem43
